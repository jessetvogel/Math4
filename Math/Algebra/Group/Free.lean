import Math.Algebra.Group.Basic

namespace Algebra.Group

-- A word of `α` is implemented as a list of pairs `(x, b)`, where `(x, True)` means `x` and `(x, False)` means `x⁻¹`
abbrev Word (α : Type _) := List (α × Bool)

-- `w * x * x⁻¹ * v ↦ w * v`
inductive Free.ReductionStep : Word α → Word α → Prop
| cancel (w₁ w₂ x b) : ReductionStep (w₁ ++ (x, b) :: (x, !b) :: w₂) (w₁ ++ w₂)

def Free (α : Type _) := Quot (@Free.ReductionStep α)

namespace Word

-- Reduce a word as much as possible (requires DecidableEq α)
def reduced [DecidableEq α] : Word α → Word α
| [] => []
| (x, b) :: cons => match reduced cons with
  | [] => [(x, b)]
  | (x', b') :: t => if x' = x ∧ b' = !b
    then t
    else (x, b) :: (x', b') :: t

-- def reduced_equiv [DecidableEq α] (w : Word α) : Free.ReductionStep w w.reduced := by {
--   match w with
--   | [] => exact Free.ReductionStep.refl [];
--   | (x, b) :: cons => {
--     unfold reduced;
--     match reduced cons with
--     | [] => {
--       dsimp;
        -- ?
--     }
--     | (x', b') :: t => sorry
--   };
-- }

end Word

namespace Free

def mul (x y : Free α) : Free α := by {
  refine Quot.lift ?f ?h₁ y;
  refine Quot.lift ?g ?h₂ x;
  exact λ w₁ w₂ => Quot.mk _ (w₁ ++ w₂);
  intro x₁ x₂ h;
  funext w₂;
    apply Quot.sound;
    cases h with
    | cancel v₁ v₂ z b => {
      have q := Free.ReductionStep.cancel v₁ (v₂ ++ w₂) z b;
      have t₁ : v₁ ++ v₂ ++ w₂ = v₁ ++ (v₂ ++ w₂) := List.append_assoc _ _ _;
      have t₂ : v₁ ++ (z, b) :: (z, !b) :: (v₂ ++ w₂) = v₁ ++ (z, b) :: (z, !b) :: v₂ ++ w₂ := by rw [← List.cons_append, ← List.cons_append, ← List.append_assoc];
      rw [← t₁, t₂] at q;
      exact q;
    };
    intro y₁ y₂ h;
    sorry;
}

def one : Free α := Quot.mk _ []

instance : Group (Free α) where
  mul := Free.mul
  one := Free.one
  mul_one x := sorry
  one_mul x := sorry
  mul_assoc x y z := sorry
  inv x := sorry
  mul_inv x := sorry

end Free

end Algebra.Group
