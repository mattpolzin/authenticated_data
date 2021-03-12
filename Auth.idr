
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
data Proof : (a : Type) -> Type where
  Nil  : SecureHashable a => Proof a
  Cons : SecureHashable a => a -> Proof a -> Proof a

namespace ReversedProof
  ||| Foorp is a reversed Proof stream.
  export
  data Foorp : (a : Type) -> Type where
    Nil  : SecureHashable a => Foorp a
    Cons : SecureHashable a => a -> Foorp a -> Foorp a

  export
  empty : SecureHashable a => Foorp a
  empty = Nil

  -- pull Foorp apart to regain SecureHashable a
  export
  (::) : a -> Foorp a -> Foorp a
  x :: Nil = Cons x Nil
  x :: xs@(Cons y z) = Cons x xs

  fromFoorp' : (first : a) -> (rest : Foorp a) -> (acc : Proof a) -> Proof a
  fromFoorp' x [] = Cons x
  fromFoorp' x (Cons y ys) = fromFoorp' y ys . Cons x

  -- pull Foorp apart to regain SecureHashable a
  export
  fromFoorp : Foorp a -> Proof a
  fromFoorp [] = []
  fromFoorp (Cons x xs) = fromFoorp' x xs []

namespace Prover
  public export
  data Elem : a -> Type where
    Hashed : Hash -> a -> Elem a

  export 
  value : Elem a -> a
  value (Hashed _ v) = v

  export
  hash : Elem a -> Hash
  hash (Hashed h _) = h

  export
  Projectable (Elem a) Hash where
    shallowProjection (Hashed hashed _) = hashed

  export
  auth : (SecureHashable b, Projectable a b) => (context : Foorp b) -> a -> (Foorp b, Elem a)
  auth ctx x = (ctx, Hashed (hash (the b (shallowProjection x))) x)

  export
  auth' : (SecureHashable b, Projectable a b) => a -> Elem a
  auth' x = Hashed (hash (the b (shallowProjection x))) x

  export
  unauth : (Projectable a b) => (context : Foorp b) -> Elem a -> (Foorp b, a)
  unauth ctx (Hashed hashed x) = ((shallowProjection x) :: ctx, x)
  
namespace Verifier
  export
  auth : SecureHashable a => (context : Proof a) -> a -> (Proof a, Hash)
  auth ctx x = (ctx, hash x)

  export
  unauth : (context : Proof a) -> Hash -> Maybe (Proof a, a)
  unauth [] x = Nothing
  unauth (Cons x ctx) hashed = case (hash x) == hashed of
                                    True  => Just $ (ctx, x)
                                    False => Nothing

data Server : (Type -> Type) -> Type -> Type where
  SAuthed : (SecureHashable a, Functor f) => f (Prover.Elem a) -> Server f a

namespace Server
  export
  fromList : {auto hashable : SecureHashable a} -> List a -> Server List a
  fromList = SAuthed . map (auth' @{(hashable, Ident)})
    where
      elem : (Hash, a) -> Elem a
      elem (hashed, x) = Hashed hashed x

  export
  authedIndex : (n : Nat) -> (Server List a) -> Maybe (Proof a, a)
  authedIndex n (SAuthed xs) = (mapFst fromFoorp) <$> authedIndex' n empty xs
    where
      authedIndex' : (n : Nat) -> (context : Foorp a) -> List (Elem a) -> Maybe (Foorp a, a)
      authedIndex' 0 _ [] = Nothing
      authedIndex' 0 ctx (x :: xs) = Just $ unauth ctx x
      authedIndex' (S k) ctx [] = Nothing
      authedIndex' (S k) ctx (x :: ys) = let (ctx', _) = unauth ctx x
                                                   in
                                                       authedIndex' k ctx' ys

data Client : (Type -> Type) -> Type -> Type where
  CAuthed : (SecureHashable a, Foldable t) => t Hash -> Client t a

namespace Client
  export
  fromList : SecureHashable a => List a -> Client List a
  fromList = CAuthed . map hash

  export
  verifiedIndex : (n : Nat) -> (clientCert : Client List a) -> (serverProof : Proof a) -> Maybe a
  verifiedIndex 0 (CAuthed []) serverProof = Nothing
  verifiedIndex 0 (CAuthed (x :: xs)) serverProof = snd <$> unauth serverProof x
  verifiedIndex (S k) (CAuthed []) serverProof = Nothing
  verifiedIndex (S k) (CAuthed (x :: xs)) [] = Nothing
  verifiedIndex (S k) (CAuthed (x :: xs)) serverProof@(Cons val serverProof') = (unauth serverProof x) *> (verifiedIndex k (CAuthed xs) serverProof')

namespace TestString
  SecureHashable String where
    hash = show

  export
  list1 : List String
  list1 = ["hello", "world", "good", "day"]

  export
  serverList : Server List String
  serverList = fromList list1

  export
  clientList : Client List String
  clientList = fromList list1

  export
  authedGood : Maybe (Proof String, String)
  authedGood = authedIndex 2 serverList

  export
  verifiedGood : Maybe String
  verifiedGood = do (serverProof, _) <- authedGood 
                    verifiedIndex 2 clientList serverProof


namespace TestInt
  SecureHashable Int where
    hash = show

  -- source of truth
  export
  list1 : List Int
  list1 = [1, 2, 3, 4, 5, 6, 7]

  -- untrusted server has this list to calculate from
  export
  serverList : Server List Int
  serverList = fromList list1

  -- client has this to verify with
  export
  clientList : Client List Int
  clientList = fromList list1

  -- server generates authed response
  export
  authedSix : Maybe (Proof Int, Int)
  authedSix = authedIndex 5 serverList

  -- client verifies server response
  export
  verifiedSix : Maybe Int
  verifiedSix = do (serverProof, _) <- authedSix
                   verifiedIndex 5 clientList serverProof

  [Obfuscated] SecureHashable Int where
    hash = show . Bits.complement . (flip Bits.setBit (Element 2 %search))

  export
  serverList2 : Server List Int
  serverList2 = fromList list1 @{Obfuscated}

  export
  clientList2 : Client List Int
  clientList2 = fromList list1 @{Obfuscated}

  export
  authedFive : Maybe (Proof Int, Int)
  authedFive = authedIndex 4 serverList2

  export
  verifiedFive : Maybe Int
  verifiedFive = do (serverProof, _) <- authedFive
                    verifiedIndex 4 clientList2 serverProof

namespace TestListListString
  SecureHashable String where
    hash = reverse

  export
  list1 : List (List String)
  list1 = [["hello", "world"], ["good", "day"]]

  export
  serverList : Server List (List String)
  serverList = fromList list1 @{ProjHash String @{FoldP}}

  export
  clientList : Client List (List String)
  clientList = fromList list1 @{ProjHash String @{FoldP}}

  export
  authedGoodDay : Maybe (Proof (List String), List String)
  authedGoodDay = authedIndex 1 serverList

  export
  verifiedGoodDay : Maybe (List String)
  verifiedGoodDay = do (serverProof, _) <- authedGoodDay 
                       verifiedIndex 1 clientList serverProof





