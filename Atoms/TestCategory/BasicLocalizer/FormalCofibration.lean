import Atoms.ForMathlib.CategoryTheory.Category.Cat.Pushout
import Atoms.ForMathlib.CategoryTheory.Comma.Arrow
import Atoms.TestCategory.BasicLocalizer.Generation
import Atoms.TestCategory.BasicLocalizer.HomotopyCocartesian
import Mathlib.CategoryTheory.Category.Cat.Colimit

open CategoryTheory Limits

namespace Atoms.TestCategory

universe u

def IsFormalCofibration {A B : Cat.{u, u}} (i : A ⟶ B) : Prop :=
  ∀ ⦃A' B' : Cat.{u, u}⦄ (α : A ⟶ A') (i' : A' ⟶ B') (β : B ⟶ B') (h : IsPushout α i i' β)
    (𝒲 : BasicLocalizer.{u}), 𝒲.IsHomotopyCocartesian h.toCommSq

theorem isFormalCofibration_iff {A B : Cat.{u, u}} (i : A ⟶ B) :
    IsFormalCofibration i ↔ ∀ ⦃A' B' : Cat.{u, u}⦄ (α : A ⟶ A') (i' : A' ⟶ B') (β : B ⟶ B')
      (h : IsPushout α i i' β), minimalBasicLocalizer.{u}.IsHomotopyCocartesian h.toCommSq :=
  ⟨fun hi _ _ α i' β h => hi α i' β h _,
    fun hi _ _ α i' β h 𝒲 => (minimalBasicLocalizer_W_iff _).1 (hi α i' β h) 𝒲⟩

structure IsDeformationRetract {A B : Cat.{u, u}} (i : A ⟶ B) : Prop where
  exists_retraction : ∃ (r : B ⟶ A) (_ : i ≫ r = 𝟙 A) (ε : r.toFunctor ⋙ i.toFunctor ⟶ 𝟭 B),
    ∀ a : A, ∃ e : i.toFunctor.obj (r.toFunctor.obj (i.toFunctor.obj a)) = i.toFunctor.obj a,
      ε.app (i.toFunctor.obj a) = eqToHom e

theorem BasicLocalizer.W_of_isDeformationRetract (𝒲 : BasicLocalizer.{u}) {A B : Cat.{u, u}}
    {i : A ⟶ B} (hi : IsDeformationRetract i) : 𝒲.W i := by
  obtain ⟨r, hr, ε, -⟩ := hi.exists_retraction
  exact 𝒲.W_of_comp_eq_id_of_W hr
    ((𝒲.W_iff_of_natTrans (u := r ≫ i) (v := 𝟙 B) ε).2 (𝒲.W.id_mem B))

theorem IsDeformationRetract.of_isPushout {A A' B B' : Cat.{u, u}} {α : A ⟶ A'} {i : A ⟶ B}
    {i' : A' ⟶ B'} {β : B ⟶ B'} (h : IsPushout α i i' β) (hi : IsDeformationRetract i) :
    IsDeformationRetract i' := by
  obtain ⟨r, hr, ε, hε⟩ := hi.exists_retraction
  have hw : α ≫ 𝟙 A' = i ≫ r ≫ α := by
    rw [Category.comp_id, ← Category.assoc, hr, Category.id_comp]
  have hr'₁ : i' ≫ h.desc (𝟙 A') (r ≫ α) hw = 𝟙 A' := h.inl_desc _ _ hw
  have e₁ : i' ≫ h.desc (𝟙 A') (r ≫ α) hw ≫ i' = i' ≫ 𝟙 B' := by
    rw [← Category.assoc, hr'₁, Category.id_comp, Category.comp_id]
  have e₂ : β ≫ h.desc (𝟙 A') (r ≫ α) hw ≫ i' = r ≫ i ≫ β := by
    rw [← Category.assoc, h.inr_desc, Category.assoc, h.w]
  obtain ⟨τ, hτ⟩ := Cat.exists_natTrans_of_isPushout h (F := h.desc (𝟙 A') (r ≫ α) hw ≫ i')
    (G := 𝟙 B') (eqToHom (congrArg Cat.Hom.toFunctor e₁))
    (eqToHom (congrArg Cat.Hom.toFunctor e₂) ≫ Functor.whiskerRight ε β.toFunctor) (fun a => by
      obtain ⟨e, he⟩ := hε a
      simp only [NatTrans.comp_app, eqToHom_app, Functor.whiskerRight_app, he, eqToHom_map,
        eqToHom_trans]
      exact Arrow.arrow_mk_eqToHom_eq _ _ (Functor.congr_obj
        (congrArg Cat.Hom.toFunctor (h.w =≫ (h.desc (𝟙 A') (r ≫ α) hw ≫ i'))) a))
  refine ⟨⟨h.desc (𝟙 A') (r ≫ α) hw, hr'₁, τ, fun a' => ?_⟩⟩
  have hτ' := hτ a'
  rw [eqToHom_app] at hτ'
  exact Arrow.exists_eq_eqToHom _ hτ'

theorem IsDeformationRetract.isFormalCofibration {A B : Cat.{u, u}} {i : A ⟶ B}
    (hi : IsDeformationRetract i) : IsFormalCofibration i :=
  fun _ _ _ _ _ h 𝒲 =>
    𝒲.isHomotopyCocartesian_of_W h.toCommSq (𝒲.W_of_isDeformationRetract hi)
      (𝒲.W_of_isDeformationRetract (hi.of_isPushout h))

theorem IsFormalCofibration.of_retract {A B C D : Cat.{u, u}} {i : A ⟶ B} {j : C ⟶ D}
    (r : RetractArrow i j) (hj : IsFormalCofibration j) : IsFormalCofibration i := by
  intro A' B' α i' β h 𝒲
  have hj' := IsPushout.of_hasPushout (r.r.left ≫ α) j
  let a : span i α ⟶ span j (r.r.left ≫ α) :=
    spanHomMk r.i.left r.i.right (𝟙 A') r.i_w.symm
      ((Category.comp_id α).trans (r.retract_left_assoc α).symm)
  let b : span j (r.r.left ≫ α) ⟶ span i α :=
    spanHomMk r.r.left r.r.right (𝟙 A') r.r_w.symm (Category.comp_id _)
  have hu : α ≫ pushout.inl (r.r.left ≫ α) j = i ≫ r.i.right ≫ pushout.inr _ _ := by
    rw [← r.i_w_assoc, ← pushout.condition, Category.assoc, r.retract_left_assoc]
    exact (Category.id_comp _).symm
  have hv : (r.r.left ≫ α) ≫ i' = j ≫ r.r.right ≫ β := by
    rw [Category.assoc, h.w, r.r_w_assoc]
  let u : B' ⟶ pushout (r.r.left ≫ α) j := h.desc _ _ hu
  let v : pushout (r.r.left ≫ α) j ⟶ B' := pushout.desc _ _ hv
  have hab : a ≫ b = 𝟙 _ := NatTrans.ext (funext fun c => by
    rcases c with _ | _ | _
    exacts [r.retract_left, r.retract_right, Category.comp_id _])
  have hm : (Grothendieck.map a).toCatHom ≫ (Grothendieck.map b).toCatHom = 𝟙 _ :=
    Cat.Hom.ext ((Grothendieck.map_comp_eq a b).symm.trans
      ((congrArg Grothendieck.map hab).trans Grothendieck.map_id_eq))
  have huv : u ≫ v = 𝟙 B' := h.hom_ext
    ((h.inl_desc_assoc _ _ _ _).trans ((pushout.inl_desc _ _ _).trans (Category.comp_id _).symm))
    (by
      rw [h.inr_desc_assoc, Category.assoc, pushout.inr_desc, r.retract_right_assoc]
      exact (Category.id_comp _).trans (Category.comp_id _).symm)
  exact 𝒲.W.of_retract
    { i := Arrow.homMk (Grothendieck.map a).toCatHom u
        (BasicLocalizer.map_comp_squareComparison h.toCommSq hj'.toCommSq a u
          (h.inr_desc _ _ _).symm
          ((Category.id_comp _).trans (h.inl_desc _ _ _).symm))
      r := Arrow.homMk (Grothendieck.map b).toCatHom v
        (BasicLocalizer.map_comp_squareComparison hj'.toCommSq h.toCommSq b v
          (pushout.inr_desc _ _ _).symm ((Category.id_comp _).trans (pushout.inl_desc _ _ _).symm))
      retract := Arrow.hom_ext _ _ hm huv }
    (hj _ _ _ hj' 𝒲)

end Atoms.TestCategory
