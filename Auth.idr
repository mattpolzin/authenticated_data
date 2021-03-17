
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
import Control.Monad.Identity

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

  -- TODO: should it encode as if just its value type?
  encodeA (_, x) = encode x

  decodeA x = let decoded = decode x
              in
                  (hash decoded, decoded)

public export
AuthType Certified where
  hashA = id

  encodeA = encode

  decodeA = decode

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
                                 in
                                     (foorp', f x)

bindp : ProverM a -> (a -> ProverM b) -> ProverM b
bindp (MkProverM runProver) f = MkProverM $ \foorp => 
                                 let (foorp', x) = runProver foorp
                                     (foorp'', x') = (f x).runProver foorp'
                                 in
                                     (foorp'', x')

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
  map f (MkVerifierM runVerifier) = MkVerifierM $ \proof => 
                                     do (proof', x) <- runVerifier proof
                                        Just (proof', f x)

bindv : VerifierM a -> (a -> VerifierM b) -> VerifierM b
bindv (MkVerifierM runVerifier) f = MkVerifierM $ \proof => 
                                     do (proof', x) <- runVerifier proof
                                        (f x).runVerifier proof'

export
[VerifierAp] Applicative VerifierM where
  pure x = MkVerifierM $ \proof => Just (proof, x)
  f <*> p = bindv f $ \f' => 
              bindv p $ \p' => MkVerifierM $ \proof => Just (proof, f' p')

export
Monad VerifierM using VerifierAp where
  (>>=) = bindv

export
[VerifierAuth] SecureHashable String => Authenticated VerifierM Certified where
  auth x = hash x

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

  ||| Prove something from the server's perspective.
  export
  prove : SecureHashable String => Encodable a => Unproven a -> (Proof, a)
  prove unproven = (mapFst fromFoorp) $ 
                     runProver (unauth unproven @{ProverAuth}) empty

namespace Verifier
  ||| Create a certified type for the given encodable type.
  export
  certified : SecureHashable String => SecureHashable a => Encodable a => a -> Certified a
  certified = auth @{VerifierAuth}

  ||| Verify proof provided by the sever against the certification
  ||| stored clientside.
  export
  verify : SecureHashable String => Encodable a => Certified a -> Proven a -> Maybe a
  verify hashed (proof, x) = snd <$> (runVerifier (unauth hashed @{VerifierAuth}) proof)

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
  verifiedString = let serverside = prove serverString
                   in 
                       verify clientString serverside

namespace ListTest
  SecureHashable String where
    hash x = x ++ x

  export
  list1 : List String
  list1 = ["hello", "world", "good", "day"]

  data L : (0 m : Type -> Type) -> (0 authty : Type -> Type) -> Type -> Type where
    Nil  : L m authty a
    Cons : a -> authty (L m authty a) -> L m authty a

  (SecureHashable a, AuthType authty) => SecureHashable (L m authty a) where
    hash [] = ""
    hash (Cons x xs) = assert_total $ hash x <+> (hash xs)

  (SecureHashable a, Encodable a, AuthType authty) => Encodable (L m authty a) where
    encode [] = ""
    encode (Cons x xs) = assert_total $ encode x <+> "," <+> (encode xs)

    decode = decodeEach . reverse . toList . (map pack) . (split (== ',')) . unpack
      where
        decodeEach : List String -> L m authty a
        decodeEach [] = Nil
        decodeEach (x :: xs) = assert_total $ 
                                 let rest = (concat . (intersperse "m")) (reverse xs)
                                 in
                                     Cons (decode x) (decode rest)

  0 AuthList : Authenticated m authty => Type -> Type
  AuthList a = authty (L m authty a)

  -- TODO: investiage why Idris cannot find the "auther" later in the same signature unless
  --       explicitly told to use it.
  export
  toAuthList : (SecureHashable a, Encodable a, AuthType authty) => {auto auther : Authenticated m authty} -> List a -> AuthList a @{auther}
  toAuthList [] = auth Nil @{auther}
  toAuthList (x :: xs) = auth (Cons x (toAuthList xs)) @{auther}

  -- TODO: here's an annoyance to look into: the need to specify the ProverAuth explicitly in the signature
  --       and in the body.
  export
  serverList : AuthList String @{ProverAuth}
  serverList = toAuthList list1 @{%search} @{ProverAuth}

  export
  clientList : AuthList String @{VerifierAuth}
  clientList = toAuthList list1 @{%search} @{VerifierAuth}

  export
  authedIndex : (SecureHashable a, Encodable a) => {auto auther : Authenticated m authty} -> (n : Nat) -> AuthList a @{auther} -> m (Maybe a)

  authedIndex' : (SecureHashable a, Encodable a) => {auto auther : Authenticated m authty} -> (n : Nat) -> L m authty a -> m (Maybe a)
  authedIndex' 0 [] = pure Nothing
  authedIndex' 0 (Cons x _) = pure $ Just x
  authedIndex' (S k) [] = pure Nothing
  authedIndex' (S k) (Cons _ xs) = authedIndex k xs

-- authedIndex forward-declared above. 
  authedIndex n xs = (unauth xs) >>= (authedIndex' n)

  export
  provenIdxZero : Proven (Maybe String)
  provenIdxZero = (mapFst fromFoorp) $ 
                    runProver (authedIndex 0 serverList @{%search} @{ProverAuth}) empty

  export
  certifiedIdxZero : Certified (Maybe String)
  certifiedIdxZero = ?h

  export
  verifiedIdxZero : Maybe String
  verifiedIdxZero = snd =<< (runVerifier (authedIndex 0 clientList {a=String} @{%search} @{VerifierAuth}) (fst provenIdxZero))

--   export
--   authedIdxZero : Maybe String
--   authedIdxZero = authedIndex 0 serverList

  

namespace TreeTest
  SecureHashable String where
    hash x = x ++ x

  data Tree : (0 m : Type -> Type) -> a -> Type where
    Leaf : Authenticated m authty => a -> Tree m a 
    Node : Authenticated m authty => authty (Tree m a) -> authty (Tree m a) -> Tree m a


