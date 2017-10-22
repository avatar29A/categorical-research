module Main

import Data.Vect

Relation : (tys : Vect arity Type) -> Type
Relation [] = Type
Relation (ty :: tys) = ty -> Relation tys

RelationOn : (ty : Type) -> (arity : Nat) -> Type
RelationOn ty arity = Relation $ replicate arity ty

data Chan : (a : Type) -> Type where
     MkChan : (ty0 : Type) -> (ty1 : Type) -> Chan (Relation [ty0, ty1])

data Cat : Type where
     MkCat : {o : Type} ->
             {a : Type} ->
             ((Relation [a, o]), (Relation [a, o]), (Relation [o, a]), (Relation [(a,a), o])) -> Cat

     MkCat2 : {o : Type} ->
              {a : Type} ->
              (a -> o, a -> o, a -> a, (a, a) -> o) -> Cat

add : Int -> Int
add x = x + 1
