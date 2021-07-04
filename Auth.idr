
--
-- This code is based on the semantics from
-- [Authenticated Data Structures, Generically](http://www.cs.umd.edu/~mwh/papers/gpads.pdf) 
--
-- Draws a lot of inspiration from
-- [Authenticated computations as a library](https://github.com/ekmett/auth/blob/master/src/Control/Monad/Auth.hs)
-- which in turn draws from
-- [Authenticated Data Structures, as a Library, for Free!](https://bentnib.org/posts/2016-04-12-authenticated-data-structures-as-a-library.html)
--

module Auth

import Data.DPair
import Data.Bits
import Data.List
import Data.List1
import Data.Vect

import Control.Monad.Identity

import Debug.Trace

%default total

public export
0 Hash : Type
Hash = String

public export
interface SecureHashable ty where
  hash : ty -> Hash

namespace Encodable
  public export
  interface Encodable a where
    encode : a -> String
    decode : String -> a

  public export
  Encodable String where
    encode = id
    decode = id

||| Proof is a list/stream of Strings that can be
||| decoded to a particular type.
export
data Proof : Type where
  Nil  : Proof
  Cons : String -> Proof -> Proof

namespace ReversedProof
  ||| Foorp is a reversed Proof stream.
  export
  data Foorp : Type where
    Nil  : Foorp 
    Cons : Encodable a => a -> Foorp -> Foorp

  export
  empty : Foorp
  empty = Nil

  -- pull Foorp apart to regain SecureHashable a
  export
  (::) : Encodable a => a -> Foorp -> Foorp
  x :: Nil = Cons x Nil
  x :: xs = Cons x xs 

  fromFoorp' : Encodable a => (first : a) -> (rest : Foorp) -> (acc : Proof) -> Proof
  fromFoorp' x Nil = Cons (encode x)
  fromFoorp' x (Cons y ys) = fromFoorp' y ys . Cons (encode x)

  -- pull Foorp apart to regain Encodable a
  export
  fromFoorp : Foorp -> Proof
  fromFoorp Nil = Nil
  fromFoorp (Cons x xs) = fromFoorp' x xs Nil

||| A type the server is holding onto but has not yet proven.
public export
0 Unproven : Type -> Type
Unproven a = (Hash, a)

||| A type the server has proven for delivery to the client.
0 Proven : Type -> Type
Proven a = (Proof, a)

||| A type the client has certified. The type param is just a marker.
public export
0 Certified : Type -> Type
Certified a = Hash

public export
interface AuthType (0 authty : Type -> Type) where
  hashA : SecureHashable a => authty a -> Hash
  encodeA : Encodable a => authty a -> String
  decodeA : (SecureHashable a, Encodable a) => String -> authty a

public export
(SecureHashable a, AuthType authty) => SecureHashable (authty a) where
  hash = hashA

public export
(SecureHashable a, Encodable a, AuthType authty) => Encodable (authty a) where
  encode = encodeA
  decode = decodeA

public export
AuthType Unproven where
  hashA (_, x)= hash x

  encodeA (hashed, _) = hashed

  -- TODO: decode not valid?
  decodeA x = let decoded = decode x
              in  (hash decoded, decoded)

public export
AuthType Certified where
  hashA = id

  encodeA = id

  decodeA = id

public export
interface (Monad m, AuthType authty) => Authenticated m authty | m where
  auth   : (SecureHashable a, Encodable a) => a -> authty a
  unauth : Encodable a => authty a -> m a

--
-- Prover
--

export
record ProverM a where
  constructor MkProverM
  runProver : Foorp -> (Foorp, a)

public export
0 Prover : Type -> Type
Prover a = ProverM (Hash, a)

export
Functor ProverM where
  map f (MkProverM runProver) = MkProverM $ \foorp => 
                                 let (foorp', x) = runProver foorp
                                 in  (foorp', f x)

bindp : ProverM a -> (a -> ProverM b) -> ProverM b
bindp (MkProverM runProver) f = MkProverM $ \foorp => 
                                 let (foorp', x) = runProver foorp
                                     (foorp'', x') = (f x).runProver foorp'
                                 in  (foorp'', x')

export
[ProverAp] Applicative ProverM where
  pure x = MkProverM $ \foorp => (foorp, x)
  f <*> p = bindp f $ \f' => 
              bindp p $ \p' => MkProverM $ \foorp => (foorp, f' p')

export
Monad ProverM using ProverAp where
  (>>=) = bindp

export
[ProverAuth] SecureHashable String => Authenticated ProverM Unproven where
  auth x = (hash (encode x), x)

  unauth (_, x) = MkProverM $ \foorp => ((encode x) :: foorp, x)


--
-- Verifier
--

record VerifierM a where
  constructor MkVerifierM
  runVerifier : Proof -> Maybe (Proof, a)

||| A Verifier for the given type. The type is just a marker.
public export
0 Verifier : Type -> Type
Verifier a = VerifierM Hash

export
Functor VerifierM where
  map f (MkVerifierM runVerifier) = MkVerifierM $ \p => 
                                     do (p', x) <- runVerifier p
                                        Just (p', f x)

bindv : VerifierM a -> (a -> VerifierM b) -> VerifierM b
bindv (MkVerifierM runVerifier) f = MkVerifierM $ \p => 
                                     do (p', x) <- runVerifier p
                                        (f x).runVerifier p'

export
[VerifierAp] Applicative VerifierM where
  pure x = MkVerifierM $ \p => Just (p, x)

  f <*> p = bindv f $ \f' => 
              bindv p $ \p' => MkVerifierM $ \p'' => Just (p'', f' p')

{-
export
Monad VerifierM using VerifierAp where
  (>>=) = bindv

export
[VerifierAuth] SecureHashable String => Authenticated VerifierM Certified where
  auth x = hash (encode x)

  unauth = MkVerifierM . checkHashed
    where
      checkHashed : Hash -> Proof -> Maybe (Proof, a)
      checkHashed hashed [] = Nothing
      checkHashed hashed (Cons x proof') = case ((hash x) == hashed) of
                                                True  => Just (proof', decode x)
                                                False => Nothing

namespace Prover
  ||| Create an unproven type for the given encodable type.
  export
  unproven : SecureHashable String => SecureHashable a => Encodable a => a -> Unproven a
  unproven = auth @{ProverAuth}

  ||| Prove any authenticated operation from the server's perspective.
  export
  prove : ProverM a -> Proven a
  prove prover = (mapFst fromFoorp) $
                   runProver prover empty

  ||| Prove a straight-forward unauth from the server's perspective.
  export
  prove' : SecureHashable String => Encodable a => Unproven a -> Proven a
  prove' unproven = prove $ unauth unproven @{ProverAuth}

namespace Verifier
  ||| Create a certified type for the given encodable type.
  export
  certified : SecureHashable String => SecureHashable a => Encodable a => a -> Certified a
  certified = auth @{VerifierAuth}

  ||| Verify a proven value provided by the server.
  export verify : VerifierM (Maybe a) -> Proven (Maybe a) -> Maybe a
  verify verifier proven = snd =<< (runVerifier verifier (fst proven))

  ||| Verify proof provided by the sever against the certification
  ||| stored clientside.
  export
  verify' : SecureHashable String => Encodable a => Certified a -> Proven a -> Maybe a
  verify' hashed proven = verify (Just <$> (unauth hashed @{VerifierAuth})) (mapSnd Just proven)

--
-- Test Cases
--

namespace StringTest
  SecureHashable String where
    hash x = x ++ x

  export
  str : String
  str = "hello"

  export
  serverString : Unproven String
  serverString = unproven str

  export
  clientString : Certified String
  clientString = certified str 

  export
  verifiedString : Maybe String
  verifiedString = let serverside = prove' serverString
                   in  verify' clientString serverside

namespace ListTest
  SecureHashable String where
    hash x = x ++ x

  list1 : List String
  list1 = ["hello", "world", "good", "day"]

  data L : (0 authty : Type -> Type) -> Type -> Type where
    Nil  : L authty a
    Cons : a -> authty (L authty a) -> L authty a

  (SecureHashable a, AuthType authty) => SecureHashable (L authty a) where
    hash [] = ""
    hash (Cons x xs) = assert_total $ hash x <+> (hash xs)

  (SecureHashable a, Encodable a, AuthType authty) => Encodable (L authty a) where
    encode [] = ""
    encode (Cons x xs) = assert_total $ encode x <+> let rest = (encode xs)
                                                     in  if rest == ""
                                                           then ""
                                                           else "," <+> rest

    decode = decodeEach . toList . (map pack) . (split (== ',')) . unpack
      where
        decodeEach : List String -> L authty a
        decodeEach [] = Nil
        decodeEach (x :: xs) = assert_total $ 
                                 let rest = (concat . (intersperse ",")) xs
                                 in  Cons (decode x) (decode rest)

  0 AuthList : (0 authty : Type -> Type) -> Type -> Type
  AuthList authty a = authty (L authty a)

  toAuthList : {auto authed : Authenticated m authty} -> (SecureHashable a, Encodable a) => List a -> AuthList authty a
  toAuthList [] = auth Nil @{authed}
  toAuthList (x :: xs) = auth (Cons x (toAuthList xs @{authed})) @{authed}

  export
  serverList : AuthList Unproven String
  serverList = toAuthList list1 @{ProverAuth}

  export
  clientList : AuthList Certified String
  clientList = toAuthList list1 @{VerifierAuth}

  authedIndex : Authenticated m authty => (SecureHashable a, Encodable a) => (n : Nat) -> AuthList authty a -> m (Maybe a)

  authedIndex' : (SecureHashable a, Encodable a, Authenticated m authty) => (n : Nat) -> L authty a -> m (Maybe a)
  authedIndex' 0 [] = pure Nothing
  authedIndex' 0 (Cons x _) = pure $ Just x
  authedIndex' (S k) [] = pure Nothing
  authedIndex' (S k) (Cons _ xs) = authedIndex k xs

-- authedIndex forward-declared above. 
  authedIndex n xs = (unauth xs) >>= (authedIndex' n)

  -- TODO: iiinteresting. so, this kind of works but I ended up with an example that verifies the server has
  --       gone _at least as far_ into the list as the requested index rather than _exactly as far_ into the
  --       list.

  -- TODO: look into why this takes ages to evaluate but :exec of an expression containing it is plenty quick.
  export
  verifiedElem : Maybe String
  verifiedElem = let idx = 1
                     serverside = prove $ authedIndex idx serverList @{ProverAuth}
                 in  verify (authedIndex idx clientList @{VerifierAuth}) serverside

||| A test of the AuthList; evaluating @verifiedElem@ takes forever but executing
||| the following test is quite snappy.
testList : IO ()
testList = printLn $ verifiedElem

namespace VectTest
  SecureHashable String where
    hash x = x ++ x

  vect1 : Vect ? String
  vect1 = ["hello", "world", "good", "day"]

  data V : (0 authty : Type -> Type) -> Nat -> Type -> Type where
    Nil  : V authty 0 a
    Cons : a -> authty (V authty n a) -> V authty (S n) a

  (SecureHashable a, AuthType authty) => SecureHashable (V authty n a) where
    hash [] = ""
    hash (Cons x xs) = assert_total $ hash x <+> (hash xs)

  -- TODO: would need to make decode failable (which it really should be) so
  --       we can talk about _trying_ to decode a vect of a certain length.
  (SecureHashable a, Encodable a, AuthType authty) => Encodable (V authty n a) where
--     encode [] = ""
--     encode (Cons x xs) = assert_total $ encode x <+> let rest = (encode xs)
--                                                      in  if rest == ""
--                                                            then ""
--                                                            else "," <+> rest
-- 
--     decode = decodeEach . toList . (map pack) . (split (== ',')) . unpack
--       where
--         decodeEach : Vect n String -> V authty n a
--         decodeEach [] = Nil
--         decodeEach (x :: xs) = assert_total $ 
--                                  let rest = (concat . (intersperse ",")) xs
--                                  in  Cons (decode x) (decode rest)

  0 AuthVect : (0 authty : Type -> Type) -> Nat -> Type -> Type
  AuthVect authty n a = authty (V authty n a)

  toAuthVect : {auto authed : Authenticated m authty} -> (SecureHashable a, Encodable a) => Vect n a -> AuthVect authty n a
  toAuthVect [] = auth Nil @{authed}
  toAuthVect (x :: xs) = auth (Cons x (toAuthVect xs @{authed})) @{authed}

  export
  serverVect : AuthVect Unproven 4 String
  serverVect = toAuthVect vect1 @{ProverAuth}

  export
  clientVect : AuthVect Certified 4 String
  clientVect = toAuthVect vect1 @{VerifierAuth}

  authedIndex : Authenticated m authty => (SecureHashable a, Encodable a) => (i : Fin n) -> AuthVect authty n a -> m (Maybe a)

  authedIndex' : (SecureHashable a, Encodable a, Authenticated m authty) => (i : Fin n) -> V authty n a -> m (Maybe a)
  authedIndex' k [] impossible
  authedIndex' FZ (Cons x _) = pure $ Just x
  authedIndex' (FS k) (Cons _ xs) = authedIndex k xs

-- authedIndex forward-declared above. 
  authedIndex n xs = (unauth xs) >>= (authedIndex' n)

  -- TODO: iiinteresting. so, this kind of works but I ended up with an example that verifies the server has
  --       gone _at least as far_ into the list as the requested index rather than _exactly as far_ into the
  --       list.

  -- TODO: look into why this takes ages to evaluate but :exec of an expression containing it is plenty quick.
  export
  verifiedElem : Maybe String
  verifiedElem = let idx = 1
                     serverside = prove $ authedIndex idx serverVect @{ProverAuth}
                 in  verify (authedIndex idx clientVect @{VerifierAuth}) serverside

||| A test of the AuthList; evaluating @verifiedElem@ takes forever but executing
||| the following test is quite snappy.
testVect : IO ()
testVect = printLn $ VectTest.verifiedElem

namespace TreeTest
  SecureHashable String where
    hash x = x ++ x

  data Tree : (0 authty : Type -> Type) -> a -> Type where
    Leaf : a -> Tree authty a 
    Node : authty (Tree authty a) -> authty (Tree authty a) -> Tree authty a

  -- TODO: SecureHashable and Encodable implementations

  0 AuthTree : (0 authty : Type -> Type) -> Type -> Type
  AuthTree authty a = authty (Tree authty a)

  


-}
