module ListStuff where

open import Agda.Primitive


data List {l} : (Set l) → Set l where
  [] : {a : Set l} → List a
  _::_ : {a : Set l} → a → List a → List a


foldr : {k l : Level} → {a : Set k} → {b : Set l} → (a → b → b) → b → List a → b
foldr f base []        = base
foldr f base (x :: xs) = f x (foldr f base xs)


map : {k l : Level} → {a : Set k} → {b : Set l} → (a → b) → List a → List b
map f []        = []
map f (x :: xs) = f x :: map f xs

_++_ : {l : Level} → {a : Set l} → List a → List a → List a
xs ++ ys = foldr (_::_) ys xs 

concat : {l : Level} → {a : Set l} → List (List a) → List a
concat = foldr (_++_) []


data HList {l} : (ts : List (Set l)) → Set l where
  [] : HList []
  _::_ : {t : Set l} → {ts : List (Set l)} → t → HList ts → HList (t :: ts)



listΠ : {l : Level} → {ts : List (Set l)} → HList (map List ts) → List (HList ts) 
listΠ {ts = []}        []           = [] :: []
listΠ {ts = (t :: ts)} (xs :: yszs) = concat (map (λ x → map (x ::_) (listΠ yszs)) xs) -- [ x :: yzs | x <- xs, yzs <- yszs ]

