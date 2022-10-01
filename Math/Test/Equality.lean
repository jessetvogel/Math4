-- Let us copy Lean's definition of `eq` to our own version of equality
inductive myeq {α : Sort u} (a : α) : α → Prop
| refl : myeq a a

-- Our goal is to show that `myeq` is an equivalence relation. That is,
-- (1) Reflexivity: for all `x : α`, we have `x ∼ x`
-- (2) Symmetry: for all `x y : α`, if `x ∼ y` then `y ∼ x`
-- (3) Transitivity: for all `x y z : α`, if `x ∼ y` and `y ∼ z` then `x ∼ z`

-- For convenience, we define an infix notation `\sim` so that we can write `x ∼ y` instead of `myeq x y`
infix:50 " ∼ " => myeq

-- We create a namespace `myeq`, so that all theorems `T` we prove will be called `myeq.T`
namespace myeq

-- Also, we define some variables, so that we don't have to write them again for each theorem
variable {X : Sort u} {x y z : X}

-- (1) Reflexivity follows by definition: it is the constructor! (That is why it is called `refl`)
example : x ∼ x := refl

-- We can use the recursor `myeq.rec` to prove that `myeq` is the smallest reflexive relation, that is,
-- for any other relation `R` on `X` such that `R x x` holds for all `x : X`, if `x ∼ y`, then also `R x y`
theorem min_refl (R : X → X → Prop) (h : ∀ x, R x x) (hxy : x ∼ y) : R x y :=
  myeq.rec (h x) hxy

/-
  # Exercises
   Replace each of the sorry's below by proofs, using only things defined in this file
   That means, using no other tactics than `exact`
-/

-- (2) Symmetry: for all `x y : α`, if `x ∼ y` then `y ∼ x`
theorem symm (hxy : x ∼ y) : y ∼ x :=
  min_refl (λ u v => v ∼ u) (λ _ => myeq.refl) hxy

-- It might be useful to prove the following lemma
theorem subst (P : X → Prop) (hxy : x ∼ y) : P x → P y :=
  min_refl (λ a b => P a → P b) (λ _ p => p) hxy

-- (3) Transitivity: for all `x y z : α`, if `x ∼ y` and `y ∼ z` then `x ∼ z`
theorem trans (hxy : x ∼ y) (hyz : y ∼ z) : x ∼ z :=
  subst (λ a => x ∼ a) hyz hxy

-- Some additional exercises:
theorem function_invariant (f : X → Sort _) (hxy : x ∼ y) : f x ∼ f y :=
  min_refl (λ a b => f a ∼ f b) (λ _ => refl) hxy

-- Why is the following theorem ill-formed?
--theorem product_invariant (hxy : x ∼ y) (t : X → Sort*) (ht : t x ∼ t y) (f : Π z : X, t z) : f x ∼ f y := sorry

def rewrite (f : X → Sort u) : x ∼ y → f x → f y := λ h₁ h₂ =>
match h₁ with
  | refl => h₂

-- Application of `rewrite`:
example (x y z : Prop) (hxy : x ∼ y) (u : x ∧ z) : (y ∧ z) := rewrite (λ a => a ∧ z) hxy u

end myeq
