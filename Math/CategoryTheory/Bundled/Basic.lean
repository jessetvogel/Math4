import Math.CategoryTheory.Basic
import Math.Algebra.Monoid.Basic

namespace CategoryTheory

structure Bundled (c : Type u → Type v) where
  type : Type u
  str : c type

structure BundledHom
  {c : Type u → Type v}
  (h : {α β : Type u} → (α → β) → c α → c β → Prop)
  (X Y : Bundled c) where
  map : X.type → Y.type
  str : h map X.str Y.str

def CategoryBundled
  (c : Type u → Type v)
  (h : {α β : Type u} → (α → β) → c α → c β → Prop) 
  (inst_id : ∀ {α : Type u} (cα : c α), h id cα cα)
  (inst_comp : ∀ {α β γ : Type u} (cα : c α) (cβ : c β) (cγ : c γ) (g : β → γ) (f : α → β) (_ : h f cα cβ) (_ : h g cβ cγ), h (g ∘ f) cα cγ)  
  : Category (Bundled c) := {
  hom := BundledHom h,
  id := λ X => {
    map := id,
    str := inst_id X.str,
  },
  comp := λ {X Y Z} g f => {
    map := g.map ∘ f.map,
    str := inst_comp X.str Y.str Z.str g.map f.map f.str g.str,
  },
  id_comp := λ f => by dsimp; congr,
  comp_id := λ f => by dsimp; congr,
  comp_assoc := λ h g f => by dsimp; congr,
}

-- TODO: change api little bit, so that last to arguments are not needed anymore..
def CatMonoid := CategoryBundled
    Algebra.Monoid
    Algebra.MonoidHom
    (λ _ => inferInstance)
    (λ cα cβ cγ g f hf hg => sorry)

#check CatMonoid

end CategoryTheory

