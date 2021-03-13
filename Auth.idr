
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
0 Hash : Type
Hash = String

public export
interface SecureHashable ty where
  hash : ty -> Hash

public export
interface SecureHashable b => Encodable a b where
  encode : a -> b
  decode : b -> a

export
data Proof : (a : Type) -> Type where
  Nil  : Encodable _ a => Proof a
  Cons : Encodable _ a => a -> Proof a -> Proof a

namespace ReversedProof
  ||| Foorp is a reversed Proof stream.
  export
  data Foorp : (a : Type) -> Type where
    Nil  : Encodable _ a => Foorp a
    Cons : Encodable _ a => a -> Foorp a -> Foorp a

  export
  empty : Encodable _ a => Foorp a
  empty @{e} = Nil @{e}

  -- pull Foorp apart to regain SecureHashable a
  export
  (::) : a -> Foorp a -> Foorp a
  x :: (Nil @{e}) = Cons x (Nil @{e}) @{e}
  x :: xs@(Cons y z @{e}) = Cons x xs @{e}

  fromFoorp' : (first : a) -> (rest : Foorp a) -> (acc : Proof a) -> Proof a
  fromFoorp' x (Nil @{e}) = Cons x @{e}
  fromFoorp' x (Cons y ys @{e}) = fromFoorp' y ys . Cons x @{e}

  -- pull Foorp apart to regain SecureHashable a
  export
  fromFoorp : Foorp a -> Proof a
  fromFoorp (Nil @{e}) = Nil @{e}
  fromFoorp (Cons x xs @{e}) = fromFoorp' x xs (Nil @{e})

public export
interface Authenticated (0 t : Type -> Type) (0 elem : Type -> Type) encoded where
  auth   : Encodable a encoded => a -> t (elem a)
  unauth : Encodable a encoded => elem a -> t a

export
record Prover encoded a where
  constructor MkProver
  runProver : Foorp encoded -> (Foorp encoded, a)

export
Authenticated (Prover encoded) (Hash,) encoded where
  auth x = MkProver $ \foorp => let encodedX = the encoded (encode x)
                                    hashed = (hash encodedX) 
                                in 
                                    (foorp, (hashed, x))

  unauth (_, x) = MkProver $ \foorp => let encodedX = the encoded (encode x)
                                       in
                                           (encodedX :: foorp, x)

export
Functor (Prover encoded) where
  map f (MkProver runProver) = MkProver $ \foorp => let (foorp', x) = runProver foorp
                                                    in
                                                        (foorp', f x)

bindp : Prover encoded a -> (a -> Prover encoded b) -> Prover encoded b
bindp (MkProver runProver) f = MkProver $ \foorp => let (foorp', x) = runProver foorp
                                                        (foorp'', x') = (f x).runProver foorp'
                                                    in
                                                        (foorp'', x')

export
Applicative (Prover encoded) where
  pure x = MkProver $ \foorp => (foorp, x)
  f <*> p = bindp f $ \f' => 
              bindp p $ \p' => MkProver $ \foorp => (foorp, f' p')

export
Monad (Prover encoded) where
  (>>=) = bindp

{-
record Verifier a where
  constructor MkVerifier
  runVerifier : Proof a -> Maybe (Proof a, a)

Authenticated Verifier (const Hash) where
  auth x = MkVerifier $ \proof => Just (proof, hash x)

  -- TODO: better type level guarantees
  unauth hashed = MkVerifier $ \case Nil           => Nothing
                                     Cons x proof' => case (hash x == hashed) of 
                                                           True  => Just (proof', x)
                                                           False => Nothing

-}

namespace Prover
  
namespace Verifier



