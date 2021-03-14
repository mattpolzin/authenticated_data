
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
import Control.Monad.Identity

%default total

public export
0 Hash : Type
Hash = String

public export
interface SecureHashable ty where
  hash : ty -> Hash

public export
interface SecureHashable a => Encodable a where
  encode : a -> String
  decode : String -> a

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
interface Monad m => Authenticated m (0 elem : Type -> Type) where
  auth   : Encodable a => a -> m (elem a)
  unauth : Encodable a => m (elem a) -> m a

export
record Prover a where
  constructor MkProver
  runProver : Foorp -> (Foorp, a)

||| Take the reversed proof output from a prover
||| (Foorp) and package it up as a Proof to send
||| to a Verifier.
export
packageProof : (Foorp, (Hash, a)) -> (Proof, a)
packageProof = bimap fromFoorp snd

export
Functor Prover where
  map f (MkProver runProver) = MkProver $ \foorp => 
                                 let (foorp', x) = runProver foorp
                                 in
                                     (foorp', f x)

bindp : Prover a -> (a -> Prover b) -> Prover b
bindp (MkProver runProver) f = MkProver $ \foorp => 
                                 let (foorp', x) = runProver foorp
                                     (foorp'', x') = (f x).runProver foorp'
                                 in
                                     (foorp'', x')

export
[ProverAp] Applicative Prover where
  pure x = MkProver $ \foorp => (foorp, x)
  f <*> p = bindp f $ \f' => 
              bindp p $ \p' => MkProver $ \foorp => (foorp, f' p')

export
Monad Prover using ProverAp where
  (>>=) = bindp

export
[ProverAuth] SecureHashable String => Authenticated Prover (Hash,) where
  auth x = MkProver $ \foorp => 
             let encodedX = encode x
                 hashed = hash encodedX 
             in 
                 (foorp, (hashed, x))

  unauth (MkProver runProver) = MkProver $ \foorp =>
                                  let (foorp', (_, x)) = runProver foorp
                                  in
                                      (foorp', x)

record Verifier a where
  constructor MkVerifier
  runVerifier : Proof -> Maybe (Proof, a)


export
Functor Verifier where
  map f (MkVerifier runVerifier) = MkVerifier $ \proof => 
                                     do (proof', x) <- runVerifier proof
                                        Just (proof', f x)

bindv : Verifier a -> (a -> Verifier b) -> Verifier b
bindv (MkVerifier runVerifier) f = MkVerifier $ \proof => 
                                     do (proof', x) <- runVerifier proof
                                        (f x).runVerifier proof'

export
[VerifierAp] Applicative Verifier where
  pure x = MkVerifier $ \proof => Just (proof, x)
  f <*> p = bindv f $ \f' => 
              bindv p $ \p' => MkVerifier $ \proof => Just (proof, f' p')

export
Monad Verifier using VerifierAp where
  (>>=) = bindv

export
[VerifierAuth] SecureHashable String => Authenticated Verifier (const Hash) where
  auth x = MkVerifier $ \proof => 
             let hashed = (hash x) 
             in 
                 Just (proof, hashed)

  unauth (MkVerifier runVerifier) = MkVerifier $ \proof =>
                                      (uncurry checkHashed) =<< runVerifier proof
    where
      checkHashed : Proof -> Hash -> Maybe (Proof, a)
      checkHashed [] hashed = Nothing
      checkHashed (Cons x proof') hashed = case ((hash x) == hashed) of
                                                True  => Just (proof', decode x)
                                                False => Nothing

namespace Prover
  
namespace Verifier

namespace StringTest

  SecureHashable String where
    hash x = x ++ x

  Encodable String where
    encode = reverse
    decode = reverse

  export
  str : Authenticated m elem => m (elem String)
  str = auth "hello"

  export
  authedString : Authenticated m elem => m (elem String) -> m (Maybe String)
  authedString x = Just <$> unauth x

  export
  serverString : Prover (Hash, String)
  serverString = str @{ProverAuth}

  export
  clientString : Verifier Hash
  clientString = str @{VerifierAuth}

  export
  verifiedString : Maybe String
  verifiedString = let serverside = runProver serverString empty 
                       payload = packageProof serverside
                   in 
                       do (Nil, _) <- runVerifier clientString (fst payload)
                            |  _ => Nothing -- there was some proof left over unexpectedly
                          pure (snd payload)

{-
namespace ListTest
  export
  list1 : List String
  list1 = ["hello", "world", "good", "day"]

  data L : (Type -> Type) -> (0 ety : Type -> Type) -> Type -> Type where
    Nil  : L m ety a
    Cons : a -> (L m ety a) -> L m ety a

  0 AuthList : Authenticated m ety => Type -> Type
  AuthList a = m (ety (L m ety a))

--   toAuthList : {auto auther : Authenticated m ety e} -> List a -> AuthList a @{auther}
--   toAuthList [] = auth ListTest.Nil @{auther}
--   toAuthList (x :: xs) = ?toAuthList_rhs_2

  index : (n : Nat) -> L m ety a -> Maybe a
  index 0 [] = Nothing
  index 0 (Cons x y) = Just x
  index (S k) [] = Nothing
  index (S k) (Cons _ xs) = index k xs

--   export
--   authedIndex : {auto auth : Authenticated m elem} -> (n : Nat) -> AuthList a @{auth} -> m (Maybe a)
--   authedIndex n xs @{e} = unauth xs @{e} >>= \xs' => pure $ index n xs'
-}

