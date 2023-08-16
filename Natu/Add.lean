import Natu.Defs

namespace Natu

open Natu

def Natu.add : Natu -> Natu -> Natu
  | zero, m => m
  | (succ n), m => Natu.succ (Natu.add n m)

instance : Add Natu where
  add := Natu.add
