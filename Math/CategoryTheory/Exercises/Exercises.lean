import Math.CategoryTheory.Basic
import Math.CategoryTheory.Functor

open CategoryTheory

variable {C : Category} {X Y Z : C.obj}

-- # Exercise
-- Prove that, for any object `X : C`, the identity morphism is the only morphism
-- such that `C.comp g f = g` for all morphisms `g : C.hom Y X`.
example (f : C.hom X X) (hf : ∀ {Y : C.obj} (g : C.hom X Y), C.comp g f = g) : f = C.id X := by {
  specialize hf (C.id X);
  rw [C.id_comp] at hf;
  exact hf;
}

-- # Exercise
-- Prove that the identity morphism on `X` is mono.
theorem id_mono : mono (C.id X) := by {
  constructor;
  intros Z g h;  
  rw [C.id_comp, C.id_comp];
  exact λ f => f;
}

-- # Exercise
-- Prove that the identity morphism on `X` is epi.
theorem id_epi : epi (C.id X) := by {
  constructor;
  intros Z g h;
  rw [C.comp_id, C.comp_id];
  exact λ f => f;
}

-- # Exercise
-- Prove that the composition of two monos is mono.
theorem comp_mono (hf : mono f) (hg : mono g) : mono (C.comp g f) := by {
  constructor;
  intros Z s t hgf;
  apply hf.cancel;
  apply hg.cancel;
  rw [C.assoc, C.assoc] at hgf;
  exact hgf;
}

-- # Exercise
-- Prove that the composition of two epis is epi.
theorem comp_epi (hf : epi f) (hg : epi g) : epi (C.comp g f) := by {
  constructor;
  intros Z s t hgf;
  apply hg.cancel;
  apply hf.cancel;
  rw [← C.assoc, ← C.assoc] at hgf;
  exact hgf;
}

-- # Exercise
-- Prove that the composition of two isomorphisms is an isomorphism.
theorem comp_iso (hf : iso f) (hg : iso g) : iso (C.comp g f) := by {
  cases hf.is_iso with | intro k hk =>
  cases hg.is_iso with | intro l hl =>
  constructor;
  apply Exists.intro (C.comp k l);
  constructor;
  rw [C.assoc, ← C.assoc l g f, hl.1, C.id_comp, hk.1];
  rw [C.assoc, ← C.assoc f k l, hk.2, C.id_comp, hl.2];
}

-- # Exercise
-- Prove that initial objects are unique up to isomorphism.
theorem initial_unique (X Y : C.obj) [hx : initial X] [hy : initial Y] : ∃ (f : C.hom X Y), iso f := by {
  -- sorry,
  cases hx.is_initial Y with | intro f hf =>
  cases hy.is_initial X with | intro g hg =>
  cases hx.is_initial X with | intro k hk =>
  cases hy.is_initial Y with | intro l hl =>
  apply Exists.intro f;
  constructor;
  apply Exists.intro g;
  constructor;
  rw [← hk (C.id X), ← hk (C.comp g f)];
  rw [← hl (C.id Y), ← hl (C.comp f g)];
}

-- # Exercise
-- Prove that terminal objects are unique up to isomorphism.
theorem terminal_unique (X Y : C.obj) [hx : terminal X] [hy : terminal Y] : ∃ (f : C.hom X Y), iso f := by {
  -- sorry,
  cases hx.is_terminal Y with | intro f hf =>
  cases hy.is_terminal X with | intro g hg =>
  cases hx.is_terminal X with | intro k hk =>
  cases hy.is_terminal Y with | intro l hl =>
  apply Exists.intro g;
  constructor;
  apply Exists.intro f;
  constructor;
  rw [← hk (C.id X), ← hk (C.comp f g)];
  rw [← hl (C.id Y), ← hl (C.comp g f)];
}

section

structure poset :=
  (α : Sort u)
  (R : α → α → Prop)
  (refl  : ∀ x, R x x)
  (asymm : ∀ {x y}, R x y → R y x → x = y)
  (trans : ∀ {x y z}, R y z → R x y → R x z)

-- # Exercise
-- Show that the type `Prop` has the structure of a partially ordered set,
-- where the relation `R` is given by implication, that is, `R P Q := P → Q`
def poset_Prop : poset := {
  α := Prop,
  R := λ P Q => P → Q,
  refl := λ P p => p, --sorry,
  asymm := λ pq qp => by dsimp; apply Eq.propIntro pq qp, --by ext; exact ⟨pq, qp⟩, -- sorry,
  trans := λ qr pq p => qr (pq p), -- sorry,
}

-- # Exercise
-- Show that every partially ordered set is naturally a category, where `hom x y`
-- is given by the proposition `x ≤ y`
def category_of_poset (P : poset) : Category := {
  obj := P.α,
  hom := λ x y => P.R x y,
  id := P.refl, -- sorry,
  comp := P.trans, -- sorry,
  comp_id := λ _ => by dsimp, -- sorry,
  id_comp := λ _ => by dsimp, -- sorry,
  assoc := λ _ _ _ => by dsimp, -- sorry,
}

end

-- # Exercise
-- Prove that a full and faithful functor reflects initial objects.
example (F : Functor C D) {Ffull : F.full} {Ffaith : F.faithful} {X : C.obj} [hFx : initial (F.obj X)] : initial X := by {
  constructor;
  intro Y;
  cases hFx.is_initial (F.obj Y) with | intro Ff hFf =>
  cases Ffull.intro Ff with | intro f hf =>
  apply Exists.intro f;
  intro g;
  specialize hFf (F.hom g);
  apply Ffaith.cancel;
  rw [← hFf, hf];
}

-- # Exercise
-- Prove that a full and faithful functor reflects terminal objects.
example (F : Functor C D) [Ffull : F.full] [Ffaith : F.faithful] {X : C.obj} [hFx : terminal (F.obj X)] : terminal X := by {
  constructor;
  intro Y;
  cases hFx.is_terminal (F.obj Y) with | intro Ff hFf =>
  cases Ffull.intro Ff with | intro f hf =>
  apply Exists.intro f;
  intro g;
  specialize hFf (F.hom g);
  apply Ffaith.cancel;
  rw [← hFf, hf];
}

-- # Exercise
-- Prove that a faithful functor reflects monos.
example (F : Functor C D) [Ffaith : F.faithful] {X Y : C.obj} {f : C.hom X Y} [hf : mono (F.hom f)] : mono f := by {
  constructor;
  intros Z g h hfgh;
  apply Ffaith.cancel;
  apply hf.cancel;
  rw [← F.map_comp, ← F.map_comp, hfgh];
}

-- # Exercise
-- Prove that a faithful functor reflects epis.
example (F : Functor C D) [Ffaith : F.faithful] {X Y : C.obj} {f : C.hom X Y} [hf : epi (F.hom f)] : epi f := by {
  constructor;
  intros Z g h hfgh;
  apply Ffaith.cancel;
  apply hf.cancel;
  rw [← F.map_comp, ← F.map_comp, hfgh];
}

-- # Exercise
-- Prove that if `F` is full and faithful, and `F X` is isomorphic to `F Y`, then `X` is isomorphic to `Y`
example (F : Functor C D) [Ffull : F.full] [Ffaith: F.faithful] {X Y : C.obj} {f : D.hom (F.obj X) (F.obj Y)} (hf : iso f) : ∃ (g : C.hom X Y), iso g := by {
  cases hf.is_iso with | intro g hg =>
  cases Ffull.intro f with | intro k hk =>
  cases Ffull.intro g with | intro l hl =>
  apply Exists.intro k;
  constructor;
  apply Exists.intro l;
  constructor;
  apply Ffaith.cancel;
  rw [F.map_comp, hk, hl, hg.1, F.map_id];
  apply Ffaith.cancel;
  rw [F.map_comp, hk, hl, hg.2, F.map_id];
}
