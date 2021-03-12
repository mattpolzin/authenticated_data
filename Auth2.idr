module Auth2

import Decidable.Equality

public export
0 Hash : Type
Hash = String

public export
interface Hashable a where
  hash : a -> Hash

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

data Proof : (b : Type) -> Type where
  Nil  : Projectable a b => Proof b
  Cons : Projectable a b => b -> Proof b -> Proof b

snoc : {auto proj : Projectable a b} -> Proof b -> b -> Proof b
snoc [] x = Cons x (Nil @{proj}) @{proj}
snoc (Cons z prf) x = Cons z (snoc prf x @{proj}) @{proj}

-- data Auth : Hashable b => Type -> Type where
--   Authed : Projectable v b => v -> Auth v {b}
-- 
-- data Unauth : Hashable b => Type -> Type where
--   Unauthed : Projectable v b => v -> Unauth v {b}

-- TODO: make Auth/Unauth foldable instead of projectable?
-- Hashable b => Projectable (Auth a {b}) b where
--   shallowProjection (Authed x) = shallowProjection x
-- 
-- Hashable b => Projectable (Unauth a {b}) b where
--   shallowProjection (Unauthed x) = shallowProjection x

namespace Prover
  public export
  data Elem : a -> Type where
    Full : (hash : Hash) -> (value : a) -> Elem a

  export
  Hashable (Elem a) where
    hash (Full hashed _) = hashed

  public export
  Projectable (Elem a) Hash where
    shallowProjection (Full hash _) = hash

  export
  auth : {auto proj : Projectable a b} -> Hashable b => a -> Elem a
  auth x = Full (hash (shallowProjection x @{proj})) x

  export
  unauth : Elem a -> a
  unauth (Full _ value) = value

  export
  prove : Hashable b => {auto proj : Projectable a b} -> (context : Proof b) -> a -> (Proof b, Elem a)
  prove context x = (context, auth x @{proj})

  export
  unauthElem : {auto proj : Projectable a b} -> (Proof b, Elem a) -> (Proof b, a)
  unauthElem (prf, (Full hash value)) = (snoc prf (shallowProjection value @{proj}) @{proj}, value)

namespace Verifier
  -- Elem is just a Hash (digest)

  export
  auth : Hashable a => a -> Hash
  auth = hash

  export
  authValue : Hashable b => (context : Proof b) -> b -> (Proof b, Hash)
  authValue context x = (context, hash x)

  -- TODO: asking to be more provably correct?
  export
  verify : Hashable b => Proof b -> Hash -> Maybe (Proof b, b)
  verify [] _ = Nothing
  verify (Cons value prf) hashed = case (decEq hashed (hash value)) of
                                            (Yes x) => Just (prf, value)
                                            (No contra) => Nothing

--
-- Playing
--

list1 : List String
list1 = ["hello", "world"]

res1 : (Proof String, Prover.Elem String)
res1 = prove (Nil @{Ident}) "hello"

list2: Prover.Elem (List String)
list2 = auth ["hello", "world"] @{Fold String}

list3 : List (Prover.Elem String)
list3 = (auth @{Ident}) <$> ["hello", "world"]

list4 : Prover.Elem (List (Prover.Elem String))
list4 = auth list3 @{Fold String}

namespace AuthList
  public export
  data AuthList : Type -> Type where
    Nil : AuthList a
    Cons : a -> Prover.Elem (AuthList a) -> AuthList a

  export
  Foldable AuthList where

  authList : {a : Type} -> (Hashable a, Monoid a) => List a -> AuthList a
  authList [] = Nil
  authList (x :: xs) = Cons x $ auth (authList xs) @{Fold a}

  export
  list1 : AuthList String
  list1 = authList ["hello", "world"]

namespace Untrusted
  export
  authedIndex : {a : Type} -> Monoid a => (n : Nat) -> (xs : AuthList a) -> Maybe (Proof a, a)
  authedIndex n xs = authedIndex' n (Nil @{Ident}) xs
    where
      authedIndex' : (n : Nat) -> (context : Proof a) -> (xs : AuthList a) -> Maybe (Proof a, a)
      authedIndex' 0 _ [] = Nothing
      authedIndex' 0 context (Cons x y) = Just $ (context, x)
      authedIndex' (S k) _ [] = Nothing
      authedIndex' (S k) context (Cons x y) = let (context', rest) = unauthElem (context, y) @{Fold a}
                                            in
                                                authedIndex' k context' rest




