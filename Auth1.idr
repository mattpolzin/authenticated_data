module Auth1

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
interface Hashable b => Projectable a b where
  shallowProjection : a -> b

public export
[Ident] Hashable a => Projectable a a where
  shallowProjection = id

public export
(Foldable t, Projectable a b, Monoid b) => Projectable (t a) b where
  shallowProjection = foldr (\e, _ => shallowProjection e) neutral

data Proof : (b : Type) -> Type where
  Nil  : Projectable a b => Proof b
  Cons : Projectable a b => b -> Proof b -> Proof b

snoc : {auto proj : Projectable a b} -> Proof b -> b -> Proof b
snoc [] x = Cons x (Nil @{proj}) @{proj}
snoc (Cons z prf) x = Cons z (snoc prf x @{proj}) @{proj}

data Auth : Hashable b => Type -> Type where
  Authed : Projectable v b => v -> Auth v {b}

data Unauth : Hashable b => Type -> Type where
  Unauthed : Projectable v b => v -> Unauth v {b}

-- TODO: make Auth/Unauth foldable instead of projectable?
Hashable b => Projectable (Auth a {b}) b where
  shallowProjection (Authed x) = shallowProjection x

Hashable b => Projectable (Unauth a {b}) b where
  shallowProjection (Unauthed x) = shallowProjection x

namespace Prover
  public export
  data Elem : a -> Type where
    Full : (hash : Hash) -> (value : a) -> Elem a

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
  prove : {auto proj : Projectable a b} -> (context : Proof b) -> a -> (Proof b, Elem a)
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
res1 = prove (Nil @{Ident}) "hello" @{Ident}

list2: Prover.Elem (List String)
list2 = auth ["hello", "world"]

