module Auth

import Decidable.Equality

public export
0 Hash : Type
Hash = String

public export
interface Hashable ty where
  hash : ty -> Hash

-- public export
-- Hashable Hash where
--   hash = id

public export
Show a => Hashable a where
  hash = show

public export
interface Projectable a b where
  shallowProjection : a -> b

public export
[Ident] Projectable a a where
  shallowProjection = id

%hint
identityProjection : Projectable a a
identityProjection = Ident

public export
[FoldP] (Foldable t, Projectable a b, Monoid b) => Projectable (t a) b where
  shallowProjection = foldr (\e, _ => shallowProjection e) neutral

public export
Fold : Foldable t => (b : Type) -> (Monoid b, Projectable a b) => Projectable (t a) b
Fold b = FoldP

export
data Proof : (a : Type) -> Type where
  Nil  : Hashable a => Proof a
  Cons : Hashable a => a -> Proof a -> Proof a

snoc : Proof a -> a -> Proof a
snoc [] x = Cons x Nil
snoc (Cons z prf) x = Cons z (snoc prf x)

namespace Prover
  public export
  data Elem : a -> Type where
    Hashed : Hash -> a -> Elem a

  export
  Projectable (Elem a) Hash where
    shallowProjection (Hashed hashed _) = hashed

  export
  auth : (Hashable b, Projectable a b) => (context : Proof b) -> a -> (Proof b, Elem a)
  auth ctx x = (ctx, Hashed (hash (the b (shallowProjection x))) x)

  export
  auth' : (Hashable b, Projectable a b) => a -> Elem a
  auth' x = Hashed (hash (the b (shallowProjection x))) x

  export
  unauth : (Projectable a b) => (context : Proof b) -> Elem a -> (Proof b, a)
  unauth ctx (Hashed hashed x) = (snoc ctx (shallowProjection x), x)
  
namespace Verifier
  export
  auth : Hashable a => (context : Proof a) -> a -> (Proof a, Hash)
  auth ctx x = (ctx, hash x)

  export
  unauth : (context : Proof a) -> Hash -> Maybe (Proof a, a)
  unauth [] x = Nothing
  unauth (Cons x ctx) hashed = case (hash x) == hashed of
                                    True  => Just $ (ctx, x)
                                    False => Nothing

data Server : (Type -> Type) -> Type -> Type where
  SAuthed : (Hashable a, Foldable t) => t (Prover.Elem a) -> Server t a

namespace Server
  export
  fromList : {auto hashable : Hashable a} -> List a -> Server List a
  fromList = SAuthed . map (auth' @{(hashable, Ident)})
    where
      elem : (Hash, a) -> Elem a
      elem (hashed, x) = Hashed hashed x

  export
  authedIndex : (n : Nat) -> (Server List a) -> Maybe (Proof a, a)
  authedIndex n (SAuthed xs) = authedIndex' n [] xs
    where
      authedIndex' : (n : Nat) -> (context : Proof a) -> List (Elem a) -> Maybe (Proof a, a)
      authedIndex' 0 _ [] = Nothing
      authedIndex' 0 ctx (x :: xs) = Just $ unauth ctx x
      authedIndex' (S k) ctx [] = Nothing
      authedIndex' (S k) ctx (x :: ys) = let (ctx', _) = unauth ctx x
                                                   in
                                                       authedIndex' k ctx' ys

data Client : (Type -> Type) -> Type -> Type where
  CAuthed : (Hashable a, Foldable t) => t Hash -> Client t a

namespace Client
  export
  fromList : Hashable a => List a -> Client List a
  fromList = CAuthed . map hash

  export
  verifiedIndex : (n : Nat) -> (clientCert : Client List a) -> (serverProof : Proof a) -> Maybe a
  verifiedIndex 0 (CAuthed []) serverProof = Nothing
  verifiedIndex 0 (CAuthed (x :: xs)) serverProof = snd <$> unauth serverProof x
  verifiedIndex (S k) (CAuthed []) serverProof = Nothing
  verifiedIndex (S k) (CAuthed (x :: xs)) [] = Nothing
  verifiedIndex (S k) (CAuthed (x :: xs)) serverProof@(Cons val serverProof') = (unauth serverProof x) *> (verifiedIndex k (CAuthed xs) serverProof')

namespace TestString
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
  -- source of truth
  export
  list1 : List Integer
  list1 = [1, 2, 3, 4, 5, 6, 7]

  -- untrusted server has this list to calculate from
  export
  serverList : Server List Integer
  serverList = fromList list1

  -- client has this to verify with
  export
  clientList : Client List Integer
  clientList = fromList list1

  -- server generates authed response
  export
  authedSix : Maybe (Proof Integer, Integer)
  authedSix = authedIndex 5 serverList

  -- client verifies server response
  export
  verifiedSix : Maybe Integer
  verifiedSix = do (serverProof, _) <- authedSix
                   verifiedIndex 5 clientList serverProof


