import Math.SetTheory.Basic
import Math.Order.Lattice.Basic

open Order

namespace SetTheory

open Set

instance : Lattice (Set α) where
  le := subset
  refl := subset_self
  asymm := subset_asymm
  trans := subset_trans
  sup := union
  le_sup_left := subset_union_left
  le_sup_right := subset_union_right
  sup_le := union_subset
  inf := inter
  inf_le_left := inter_subset_left
  inf_le_right := inter_subset_right
  le_inf := subset_inter

end SetTheory
