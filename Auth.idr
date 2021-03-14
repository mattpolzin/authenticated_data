
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
interface Monad m => Authenticated m (0 ety : Type -> Type) where
  auth   : Encodable a => a -> m (ety a)
  unauth : Encodable a => m (ety a) -> m a

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
[ProverAuth] SecureHashable String => Authenticated ProverM (Hash,) where
  auth x = MkProverM $ \foorp => 
             let encodedX = encode x
                 hashed = hash encodedX 
             in 
                 (foorp, (hashed, x))

  unauth (MkProverM runProver) = MkProverM $ \foorp =>
                                  let (foorp', (_, x)) = runProver foorp
                                  in
                                      (foorp', x)

%hint
public export
ProverAuthHint : (SecureHashable String, Encodable a) => Authenticated ProverM (Hash,)
ProverAuthHint = ProverAuth

record VerifierM decoded a where
  constructor MkVerifierM
  runVerifier : Proof -> Maybe (Proof, a)

public export
0 Verifier : Type -> Type
Verifier a = VerifierM a Hash

export
Functor (VerifierM d) where
  map f (MkVerifierM runVerifier) = MkVerifierM $ \proof => 
                                     do (proof', x) <- runVerifier proof
                                        Just (proof', f x)

bindv : VerifierM d a -> (a -> VerifierM d b) -> VerifierM d b
bindv (MkVerifierM runVerifier) f = MkVerifierM $ \proof => 
                                     do (proof', x) <- runVerifier proof
                                        (f x).runVerifier proof'

export
[VerifierAp] Applicative (VerifierM d) where
  pure x = MkVerifierM $ \proof => Just (proof, x)
  f <*> p = bindv f $ \f' => 
              bindv p $ \p' => MkVerifierM $ \proof => Just (proof, f' p')

export
Monad (VerifierM d) using VerifierAp where
  (>>=) = bindv

export
[VerifierAuth] SecureHashable String => Authenticated (VerifierM d) (const Hash) where
  auth x = MkVerifierM $ \proof => 
             let hashed = (hash x) 
             in 
                 Just (proof, hashed)

  unauth (MkVerifierM runVerifier) = MkVerifierM $ \proof =>
                                      (uncurry checkHashed) =<< runVerifier proof
    where
      checkHashed : Proof -> Hash -> Maybe (Proof, a)
      checkHashed [] hashed = Nothing
      checkHashed (Cons x proof') hashed = case ((hash x) == hashed) of
                                                True  => Just (proof', decode x)
                                                False => Nothing

%hint
public export
VerifierAuthHint : (SecureHashable String, Encodable d) => (Encodable d, Authenticated (VerifierM d) (const Hash))
VerifierAuthHint @{(_, e)}= (e, VerifierAuth)

export
authed : (Encodable a, Authenticated m authty) => a -> m (authty a)
authed x @{(_, auther)} = auth x @{auther}

namespace Prover
  ||| Create a prover for the given encodable type.
  export
  prover : (SecureHashable String, Encodable a) => a -> Prover a
  prover = authed

  ||| Take the reversed proof output from a prover
  ||| (Foorp) and package it up as a Proof to send
  ||| to a Verifier.
  export
  packageProof : (Foorp, (Hash, a)) -> (Proof, a)
  packageProof = bimap fromFoorp snd

namespace Verifier
  ||| Create a verifier for the given encodable type.
  export
  verifier : (SecureHashable String, Encodable a) => a -> Verifier a
  verifier = authed @{VerifierAuthHint}

namespace StringTest
  SecureHashable String where
    hash x = x ++ x

  Encodable String where
    encode = reverse
    decode = reverse

  export
  str : String
  str = "hello"

  export
  serverString : Prover String
  serverString = prover str

  export
  clientString : Verifier String
  clientString = verifier str 

  export
  verifiedString : Maybe String
  verifiedString = let serverside = runProver serverString empty 
                       payload = packageProof serverside
                   in 
                       do (Nil, _) <- runVerifier clientString (fst payload)
                            |  _ => Nothing -- there was some proof left over unexpectedly
                          pure (snd payload)

namespace ListTest
  export
  list1 : List String
  list1 = ["hello", "world", "good", "day"]

  data L : (0 m : Type -> Type) -> (0 authty : Type -> Type) -> Type -> Type where
    Nil  : L m authty a
    Cons : m (authty a) -> (L m authty a) -> L m authty a

  0 AuthList : Authenticated m authty => Type -> Type
  AuthList a = m (authty (L m authty a))

--   toAuthList : Authenticated m ety e} -> List a -> AuthList a @{auther}
--   toAuthList [] = auth ListTest.Nil @{auther}
--   toAuthList (x :: xs) = ?toAuthList_rhs_2

--   index : (n : Nat) -> L m ety a -> Maybe a
--   index 0 [] = Nothing
--   index 0 (Cons x y) = Just x
--   index (S k) [] = Nothing
--   index (S k) (Cons _ xs) = index k xs

--   export
--   authedIndex : {auto auth : Authenticated m elem} -> (n : Nat) -> AuthList a @{auth} -> m (Maybe a)
--   authedIndex n xs @{e} = unauth xs @{e} >>= \xs' => pure $ index n xs'

