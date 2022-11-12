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
  lub := union
  le_lub_left := subset_union_left
  le_lub_right := subset_union_right
  lub_le := union_subset
  glb := inter
  glb_le_left := inter_subset_left
  glb_le_right := inter_subset_right
  le_glb := subset_inter

end SetTheory
