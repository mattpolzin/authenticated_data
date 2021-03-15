
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

public export
data AuthMode = ServerAuth | ClientAuth

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
0 AuthModeType : AuthMode -> Type -> Type
AuthModeType ServerAuth = Unproven
AuthModeType ClientAuth = Certified

public export
SecureHashable a => SecureHashable (Unproven a) where
  hash (_, x) = hash x

public export
SecureHashable a => SecureHashable (Certified a) where
  hash = id

public export
(SecureHashable a, Encodable a) => Encodable (Unproven a) where
  encode (_, x) = encode x
  decode = (mapFst hash) . dup . (the (String -> a) decode)

-- currently covered by (Encodable String) until or unless
-- Hash becomes something other than an alias for String.
-- public export
-- Encodable a => Encodable (Certified a) where

public export
interface Monad m => Authenticated m (0 am : AuthMode) | m where
  auth   : (SecureHashable a, Encodable a) => a -> (AuthModeType am) a
  unauth : Encodable a => (AuthModeType am) a -> m a

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
[ProverAuth] SecureHashable String => Authenticated ProverM ServerAuth where
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
[VerifierAuth] SecureHashable String => Authenticated VerifierM ClientAuth where
  auth x = hash x

  unauth = MkVerifierM . checkHashed
    where
      checkHashed : Hash -> Proof -> Maybe (Proof, a)
      checkHashed hashed [] = Nothing
      checkHashed hashed (Cons x proof') = case ((hash x) == hashed) of
                                                True  => Just (proof', decode x)
                                                False => Nothing

export
authed : Authenticated m mode => (SecureHashable a, Encodable a) => a -> (AuthModeType mode) a
authed x @{auther} = auth x @{auther}

namespace Prover
  ||| Create an unproven type for the given encodable type.
  export
  unproven : SecureHashable String => SecureHashable a => Encodable a => a -> Unproven a
  unproven = authed @{ProverAuth}

  ||| Prove something from the server's perspective.
  export
  prove : SecureHashable String => Encodable a => Unproven a -> (Foorp, a)
  prove unproven = runProver (unauth unproven @{ProverAuth}) empty

  ||| Take the reversed proof output from a prover
  ||| (Foorp) and package it up as a Proof to send
  ||| to a Verifier.
  export
  packageProof : (Foorp, a) -> Proven a
  packageProof = mapFst fromFoorp

namespace Verifier
  ||| Create a certified type for the given encodable type.
  export
  certified : SecureHashable String => SecureHashable a => Encodable a => a -> Certified a
  certified = authed @{VerifierAuth}

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
                       payload = packageProof serverside
                   in 
                       verify clientString payload

namespace ListTest
  SecureHashable String where
    hash x = x ++ x

  export
  list1 : List String
  list1 = ["hello", "world", "good", "day"]

  data L : (0 m : Type -> Type) -> (0 mode : AuthMode) -> Type -> Type where
    Nil  : L m mode a
    Cons : a -> (AuthModeType mode) (L m mode a) -> L m mode a

  [SecHashS] (SecureHashable a, SecureHashable (Unproven a)) => SecureHashable (L m ServerAuth a) where
    hash [] = ""
    hash (Cons x (_, xs)) = (hash x) <+> (hash xs)

  [SecHashC] SecureHashable a => SecureHashable (L m ClientAuth a) where
    hash [] = ""
    hash (Cons x hashed) = (hash x) <+> hashed

  [EncS] Encodable a => Encodable (L m ServerAuth a) where
    encode [] = ""
    encode (Cons x (_, xs)) = (encode x) <+> "," <+> (encode xs)

    decode = decodeEach . reverse . toList . (map pack) . (split (== ',')) . unpack 
      where
        decodeEach : List String -> L m ServerAuth a
        decodeEach [] = Nil
        decodeEach (x :: xs) = let rest = decodeEach xs
                               in
                                   Cons (decode x) (hash (encode rest), rest)

  [EncC] (SecureHashable a, Encodable a) => Encodable (L m ClientAuth a) where
    encode [] = ""
    encode (Cons x y) = (encode x) <+> "|" <+> y

    decode = decodeEach . reverse . toList . (map pack) . (split (== '|')) . unpack
      where
        decodeEach : List String -> L m ClientAuth a
        decodeEach [] = Nil
        decodeEach (x :: xs) = Cons (decode x) (hash (decodeEach xs) @{SecHashC})


  0 AuthList : Authenticated m mode => Type -> Type
  AuthList a = L m mode a

  -- TODO: investiage why Idris cannot find the "auther" later in the same signature unless
  --       explicitly told to use it.
  export
  toAuthList : (SecureHashable a, Encodable a) => {mode : AuthMode} -> {auto auther : Authenticated m mode} -> List a -> AuthList a @{auther}
  toAuthList {mode} [] = ListTest.Nil
  toAuthList {mode = ServerAuth} (x :: xs) = Cons x (auth (toAuthList xs) @{auther} @{(SecHashS, EncS)})
  toAuthList {mode = ClientAuth} (x :: xs) = Cons x (auth (toAuthList xs {auther}) @{auther} @{(SecHashC, EncC)})

  -- TODO: here's an annoyance to look into: the need to specify the ProverAuth explicitly in the signature
  --       and in the body.
  export
  serverList : AuthList String @{ProverAuth}
  serverList = toAuthList list1 @{%search} @{ProverAuth}

  export
  clientList : AuthList String @{VerifierAuth}
  clientList = toAuthList list1 @{%search} @{VerifierAuth}

  export
  authedIndex : {auto auth : Authenticated m elem} -> (n : Nat) -> AuthList a @{auth} -> m (Maybe a)
  authedIndex 0 [] = pure Nothing
  authedIndex 0 (Cons x y) = pure $ Just x
  authedIndex (S k) [] = pure Nothing
  authedIndex (S k) (Cons _ xs) = ?h_2

