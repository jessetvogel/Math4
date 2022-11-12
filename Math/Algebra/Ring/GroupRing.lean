-- import Math.Algebra.Ring.Basic
-- import Math.Algebra.FinSupport

-- open SetTheory

-- namespace Algebra

-- variable (α : Type u) [R : Ring α] (β : Type v) [G : Group β]

-- abbrev GroupRing := FinSupport β α

-- def GroupRing.of_single {α : Type u} [R : Ring α] {β : Type v} [G : Group β] [DecidableEq β] (x : β) : GroupRing α β := {
--   map := λ y => if y = x then 1 else 0,
--   support := FinSet.of_single x,
--   fin_support := by {
--     intro y;
--     constructor;
--     intro hy;
--     sorry; -- TODO: must change definition of map
--     intro hy;
--     sorry; -- TODO: must change definition of map
--   }
-- }

-- instance [DecidableEq β] : Ring (GroupRing α β) where
--   add := FinSupport.add
--   zero := FinSupport.zero
--   mul := FinSupport.mul
--   one := GroupRing.of_single 1
--   neg := FinSupport.neg
--   add_assoc := sorry
--   add_comm := sorry
--   add_zero := sorry --FinSupport.add_zero
--   add_neg := sorry
--   mul_assoc := sorry
--   mul_one := sorry
--   one_mul := sorry
--   distrib_left := sorry
--   distrib_right := sorry

-- instance : Coe β (GroupRing α β) where
--   coe := GroupRing.of_single

-- end Algebra
