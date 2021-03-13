

--
--
-- This one hit a big snag because I am not happy with needed to be able to deserialize from
-- proofs to get values back but I cannot use proofs with values in them along with monads which
-- require that the proof type stays static while mapping/applying/binding.
--
--

--
-- This code is based on the semantics from
-- [Authenticated Data Structures, Generically](http://www.cs.umd.edu/~mwh/papers/gpads.pdf) 
--

module Auth

import Data.DPair
import Data.Bits
import Data.List
import Control.Monad.Identity

%default total

public export
Hash : Type
Hash = String

public export
interface SecureHashable ty where
  hash : ty -> Hash

public export
interface Projectable a b where
  shallowProjection : a -> b

public export
[ProjH] (SecureHashable b, Projectable a b) => SecureHashable a where
  hash x = hash $ (the b $ shallowProjection x)

public export
ProjHash : (b : Type) -> {auto p : Projectable a b} -> {auto h : SecureHashable b} -> SecureHashable a
ProjHash _ = ProjH @{(h, p)}

public export
[Ident] Projectable a a where
  shallowProjection = id

%hint
identityProjection : Projectable a a
identityProjection = Ident

public export
[FoldP] (Foldable t, Projectable a b, Monoid b) => Projectable (t a) b where
  shallowProjection = foldr (\e, acc => shallowProjection e <+> acc) neutral

public export
Fold : Foldable t => (b : Type) -> (Monoid b, Projectable a b) => Projectable (t a) b
Fold b = FoldP

export
data Proof : Type -> Type where
  Nil  : Proof a
  Cons : a -> Proof a -> Proof a

namespace ReversedProof
  ||| Foorp is a reversed Proof stream.
  export
  data Foorp : Type -> Type where
    Nil  : Foorp a
    Cons : a -> Foorp a -> Foorp a

  export
  empty : Foorp a
  empty = Nil

  export
  (::) : a -> Foorp a -> Foorp a
  x :: Nil = Cons x Nil
  x :: xs@(Cons y z) = Cons x xs

public export
interface Monad m => MonadAuth m (elem : Type -> Type) where
  auth : SecureHashable a => a -> m (elem a)
  unauth : elem a -> (m a)

export
record Prover a where
  constructor MkProver
  runProver : Foorp a -> (Foorp a, a)

-- export
-- Functor Prover where
--   map f (MkProver runProver) = MkProver $ \foorp => (mapSnd f) $ runProver foorp

bindp : Prover a -> (a -> Prover b) -> Prover b
bindp (MkProver runProver) f = 
  MkProver $ \foorp => 
    let (foorp', a) = runProver foorp
        (MkProver runProver') = f a
    in
        runProver' foorp'

namespace ProverMonad
  export
  (>>=) : Prover a -> (a -> Prover b) -> Prover b
  (>>=) = bindp

{-

-- export
-- Applicative Prover where
--   pure x = MkProver $ \s => (s, x)
-- 
-- -- TODO: does it matter what order I bind f and a in?
--   f <*> a = bindp a $ 
--               \a' => bindp f $
--                 \f' => MkProver $ \foorp => (foorp, f' a')

-- export
-- Monad Prover where
--   (>>=) = bindp

export
MonadAuth Prover (Hash,) False where
  -- TODO: account for using (hash (shallowProjection x)) instead of just hash
  auth x = MkProver $ \foorp => (foorp, (hash x, x))

  unauth (hashed, x) = MkProver $ \foorp => (hashed :: foorp, x)

export
record Verifier a where
  constructor MkVerifier
  runVerifier : Proof a -> Maybe (Proof a, a)

-- export
-- Functor Verifier where
--   map f (MkVerifier runVerifier) = MkVerifier $ \proof => (mapSnd f) <$> runVerifier proof

bindv : Verifier a -> (a -> Verifier b) -> Verifier b
bindv (MkVerifier runVerifier) f = 
  MkVerifier $ \proof => do
    (proof', a) <- runVerifier proof
    let (MkVerifier runVerifier') = f a
    runVerifier' proof'

namespace Verifier
  export
  (>>=) : Verifier a -> (a -> Verifier b) -> Verifier b
  (>>=) = bindp

-- export
-- Applicative Verifier where
--   pure x = MkVerifier $ \s => Just (s, x)
--   
-- -- TODO: does it matter what order I bind f and a in?
--   f <*> a = bindv a $ 
--               \a' => bindv f $
--                 \f' => MkVerifier $ \proof => Just (proof, f' a')

-- export
-- Monad Verifier where
--   (>>=) = bindv

export
MonadAuth Verifier (const Hash) False where
  auth x = MkVerifier $ \proof => Just (proof, hash x)

  -- TODO: use dependent types to larger efficacy
  unauth hashed = MkVerifier $ \case Nil         => Nothing
                                     (Cons x xs) => case (x == hashed) of
                                                         True  => Just (xs, ?h)
                                                         False => Nothing



-}
