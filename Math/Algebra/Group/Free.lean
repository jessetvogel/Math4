import Math.Algebra.Group.Basic

namespace Algebra.Group

namespace Free

-- A word of `α` is implemented as a list of pairs `(x, b)`, where `(x, True)` means `x` and `(x, False)` means `x⁻¹`
abbrev Word (α : Type _) := List (α × Bool)
-- `w * x * x⁻¹ * v ↦ w * v`
inductive ReductionStep : Word α → Word α → Prop
| cancel {w₁ w₂ x b} : ReductionStep (w₁ ++ (x, b) :: (x, !b) :: w₂) (w₁ ++ w₂)

end Free

def Free (α : Type _) := Quot (@Free.ReductionStep α)

namespace Free

-- Reduce a word as much as possible
-- def reduce [DecidableEq α] : Word α → Word α
-- | [] => []
-- | [(x, b)] => [(x, b)]
-- | (x₁, b₁) :: (x₂, b₂) :: cons => ???

end Free

end Algebra.Group
