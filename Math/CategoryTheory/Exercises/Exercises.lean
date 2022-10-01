import Math.CategoryTheory.Category

-- # Exercise
-- Prove that, for any object `X : C`, the identity morphism is the only morphism
-- such that `C.comp g f = g` for all morphisms `g : C.hom Y X`.
example (f : C.hom X X) (hf : ∀ {Y : C.obj} (g : C.hom X Y), C.comp g f = g) : f = C.id X := by {
  -- sorry,
  specialize hf (C.id X);
  rw [C.id_comp] at hf;
  exact hf;
}

-- # Exercise
-- Prove that the identity morphism on `X` is mono.
theorem id_mono : mono (C.id X) := by {
  -- sorry,
  constructor;
  intros Z g h;
  rw [C.id_comp, C.id_comp];
  exact λ f => f;
}

-- # Exercise
-- Prove that the identity morphism on `X` is epi.
theorem id_epi : epi (C.id X) := by {
  -- sorry,
  constructor;
  intros Z g h;
  rw [C.comp_id, C.comp_id];
  exact λ f => f;
}

-- # Exercise
-- Prove that the composition of two monos is mono.
theorem comp_mono (hf : mono f) (hg : mono g) : mono (C.comp g f) := by {
  -- sorry,
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
  -- sorry,
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
  -- sorry,
  cases hf.inv with | intro k hk =>
  cases hg.inv with | intro l hl =>
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
  cases initial_map X Y with | intro f hf =>
  cases initial_map Y X with | intro g hg =>
  cases initial_map X X with | intro k hk =>
  cases initial_map Y Y with | intro l hl =>
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
  cases terminal_map X Y with | intro f hf =>
  cases terminal_map Y X with | intro g hg =>
  cases terminal_map X X with | intro k hk =>
  cases terminal_map Y Y with | intro l hl =>
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
example (F : functor C D) [full F] [faithful F] {X : C.obj} [initial (F.obj X)] : initial X :=
begin
  -- sorry,
  constructor,
  intro Y,
  cases initial_map (F.obj X) (F.obj Y) with Ff hFf,
  cases full.intro Ff with f hf,
  use f,
  intro g,
  specialize hFf (F.map g),
  apply @faithful.cancel _ _ F _ _ _ f g,
  rw [← hFf, hf],
end

-- # Exercise
-- Prove that a full and faithful functor reflects terminal objects.
example (F : functor C D) [full F] [faithful F] {X : C.obj} (hx : terminal (F.obj X)) : terminal X :=
begin
  -- sorry,
  constructor,
  intro Y,
  cases terminal_map (F.obj X) (F.obj Y) with Ff hFf,
  cases full.intro Ff with f hf,
  use f,
  intro g,
  specialize hFf (F.map g),
  apply @faithful.cancel _ _ F _ _ _ f g,
  rw [← hFf, hf],
end

-- # Exercise
-- Prove that a faithful functor reflects monos.
example (F : functor C D) [faithful F] {X Y : C.obj} {f : C.hom X Y} [hf : mono (F.map f)] : mono f :=
begin
  -- sorry,
  constructor,
  intros Z g h hfgh,
  apply @faithful.cancel _ _ F _ _ _ g h,
  apply hf.cancel,
  rw [← F.map_comp, ← F.map_comp, hfgh],
end

-- # Exercise
-- Prove that a faithful functor reflects epis.
example (F : functor C D) [faithful F] {X Y : C.obj} {f : C.hom X Y} [hf : epi (F.map f)] : epi f :=
begin
  -- sorry,
  constructor,
  intros Z g h hfgh,
  apply @faithful.cancel _ _ F _ _ _ g h,
  apply hf.cancel,
  rw [← F.map_comp, ← F.map_comp, hfgh],
end

-- # Exercise
-- Prove that if `F` is full and faithful, and `F X` is isomorphic to `F Y`, then `X` is isomorphic to `Y`
example (F : functor C D) [full F] [faithful F] {X Y : C.obj} {f : D.hom (F.obj X) (F.obj Y)} (hf : iso f) : ∃ (g : C.hom X Y), iso g :=
begin
  -- sorry,
  cases hf.inv with g hg,
  cases full.intro f with k hk,
  cases full.intro g with l hl,
  use k,
  use l,
  split,
  apply @faithful.cancel _ _ F,
  rw [F.map_comp, hk, hl, hg.1, F.map_id],
  apply @faithful.cancel _ _ F,
  rw [F.map_comp, hk, hl, hg.2, F.map_id],
end