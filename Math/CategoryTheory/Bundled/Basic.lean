import Math.CategoryTheory.Basic
import Math.Algebra.Monoid.Basic

namespace CategoryTheory

structure Bundled (c : Type u → Type v) where
  type : Type u
  str : c type

set_option checkBinderAnnotations false in -- so that `[str : c α]` works even though `c α` is not a typeclass
def Bundled.of {c : Type u → Type v} (α : Type u) [str : c α] : Bundled c where
  type := α
  str := str

class BundledHom
  {c : Type u → Type v}
  (h : {α β : Type u} → (α → β) → c α → c β → Prop) where
  id : ∀ {α : Type u} (cα : c α), h id cα cα
  comp : ∀ {α β γ : Type u} {cα : c α} {cβ : c β} {cγ : c γ} {g : β → γ} {f : α → β} (_ : h f cα cβ) (_ : h g cβ cγ), h (g ∘ f) cα cγ

structure BundledMap
  {c : Type u → Type v}
  (h : {α β : Type u} → (α → β) → c α → c β → Prop)
  [BundledHom h]
  (X Y : Bundled c)
  where
  map : X.type → Y.type
  str : h map X.str Y.str

def CatBundled
  (c : Type u → Type v)
  (h : {α β : Type u} → (α → β) → c α → c β → Prop) 
  [inst : BundledHom h] : Category (Bundled c) where
  hom := BundledMap h
  id X := {
    map := id,
    str := inst.id X.str,
  }
  comp g f := {
    map := g.map ∘ f.map,
    str := inst.comp f.str g.str,
  }
  id_comp f := by dsimp; congr
  comp_id f := by dsimp; congr
  comp_assoc h g f := by dsimp; congr

end CategoryTheory

