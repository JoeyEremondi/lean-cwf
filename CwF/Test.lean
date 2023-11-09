inductive Term where
  | Foo : String → Term
  | NApp : List Term → Term

open List
open Term

def fv : (t : Term) → List String
  | (Foo x) => cons x List.nil
  | (NApp ts) => join (map fv ts)
