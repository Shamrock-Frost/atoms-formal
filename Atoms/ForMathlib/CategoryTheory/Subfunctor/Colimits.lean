import Mathlib.CategoryTheory.Limits.Types.Multicoequalizer
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Subfunctor.Image

universe w v u

namespace CategoryTheory.Subfunctor

open Limits

variable {C : Type u} [Category.{v} C]

theorem isPushout_of_bicartSq {X : Cᵒᵖ ⥤ Type w} {A₁ A₂ A₃ A₄ : Subfunctor X}
    (sq : Lattice.BicartSq A₁ A₂ A₃ A₄) :
    IsPushout (Subfunctor.homOfLe sq.le₁₂) (Subfunctor.homOfLe sq.le₁₃)
      (Subfunctor.homOfLe sq.le₂₄) (Subfunctor.homOfLe sq.le₃₄) where
  w := rfl
  isColimit' :=
    ⟨evaluationJointlyReflectsColimits _ fun a =>
      (PushoutCocone.isColimitMapCoconeEquiv _ _).2
        (Types.isPushout_of_bicartSq (S₁ := A₁.obj a) (S₂ := A₂.obj a) (S₃ := A₃.obj a)
          (S₄ := A₄.obj a) ⟨by rw [← sq.sup_eq]; rfl, by rw [← sq.inf_eq]; rfl⟩).isColimit⟩

theorem isPushout_of_preimage {Z K : Cᵒᵖ ⥤ Type w} (S : Subfunctor Z) (φ : K ⟶ Z)
    {R : Subfunctor K} (hR : S.preimage φ = R) {T : Subfunctor Z}
    (hT : S ⊔ Subfunctor.range φ = T)
    (hφ : ∀ (k : Cᵒᵖ) (x y : K.obj k), x ∉ R.obj k → y ∉ R.obj k →
      φ.app k x = φ.app k y → x = y) :
    IsPushout R.ι (Subfunctor.lift (R.ι ≫ φ) (by subst hR; exact fun k _ ⟨⟨_, hx⟩, h⟩ ↦ h ▸ hx))
      (Subfunctor.lift φ (hT ▸ le_sup_right)) (Subfunctor.homOfLe (hT ▸ le_sup_left)) := by
  subst hR hT
  refine IsPushout.flip ⟨⟨rfl⟩, ⟨evaluationJointlyReflectsColimits _ fun k ↦ ?_⟩⟩
  refine (isColimitMapCoconePushoutCoconeEquiv _ _).2 (IsPushout.isColimit ?_)
  refine Types.isPushout_of_isPullback_of_mono' ?_ ?_ ?_
  · rw [Types.isPullback_iff]
    refine ⟨rfl, fun x y h ↦ Subtype.ext h.2, fun a x h ↦ ⟨⟨x, ?_⟩, ?_, rfl⟩⟩
    · have h' := congrArg Subtype.val h
      exact (h' ▸ a.2 : _)
    · exact Subtype.ext (congrArg Subtype.val h).symm
  · refine Set.eq_univ_of_forall fun ⟨x, hx⟩ ↦ ?_
    rcases hx with hx | ⟨y, rfl⟩
    · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
    · exact Or.inr ⟨y, rfl⟩
  · intro x y hx hy h
    refine hφ k x y (fun h' ↦ hx ⟨⟨x, h'⟩, rfl⟩) (fun h' ↦ hy ⟨⟨y, h'⟩, rfl⟩) ?_
    exact congrArg Subtype.val h

variable {X Y Z W V : Cᵒᵖ ⥤ Type w}

theorem range_desc_of_isColimit {J : Type*} [Category* J] [HasColimitsOfShape J (Type w)]
    {F : J ⥤ Cᵒᵖ ⥤ Type w} {c : Cocone F} (hc : IsColimit c) (s : Cocone F) :
    Subfunctor.range (hc.desc s) = ⨆ j, Subfunctor.range (s.ι.app j) := by
  ext T x
  simp only [Subfunctor.range_obj, Subfunctor.iSup_obj, Set.mem_range, Set.mem_iUnion]
  have h := fun j (z : (F.obj j).obj T) =>
    ConcreteCategory.congr_hom (NatTrans.congr_app (hc.fac s j) T) z
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨j, z, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves ((evaluation _ _).obj T) hc) y
    exact ⟨j, z, (h j z).symm⟩
  · rintro ⟨j, z, rfl⟩
    exact ⟨(c.ι.app j).app T z, h j z⟩

theorem range_pushout_desc (f : X ⟶ Y) (g : X ⟶ Z) (a : Y ⟶ W) (b : Z ⟶ W)
    (w : f ≫ a = g ≫ b) [HasPushout f g] :
    Subfunctor.range (pushout.desc a b w) = Subfunctor.range a ⊔ Subfunctor.range b := by
  refine (range_desc_of_isColimit (pushoutIsPushout f g) (PushoutCocone.mk a b w)).trans
    (le_antisymm (iSup_le fun j => ?_)
      (sup_le (le_iSup_of_le .left le_rfl) (le_iSup_of_le .right le_rfl)))
  rcases j with _ | _ | _
  · exact (Subfunctor.range_comp_le f a).trans le_sup_left
  · exact le_sup_left
  · exact le_sup_right

theorem range_coprod_desc (a : X ⟶ W) (b : Y ⟶ W) [HasBinaryCoproduct X Y] :
    Subfunctor.range (coprod.desc a b) = Subfunctor.range a ⊔ Subfunctor.range b := by
  refine (range_desc_of_isColimit (coprodIsCoprod X Y) (BinaryCofan.mk a b)).trans
    (le_antisymm (iSup_le fun ⟨j⟩ => ?_)
      (sup_le (le_iSup_of_le ⟨.left⟩ le_rfl) (le_iSup_of_le ⟨.right⟩ le_rfl)))
  rcases j with _ | _
  · exact le_sup_left
  · exact le_sup_right

theorem range_pushout_desc_comp (f : X ⟶ Y) (g : X ⟶ Z) (a : Y ⟶ W) (b : Z ⟶ W)
    (w : f ≫ a = g ≫ b) (h : W ⟶ V) [HasPushout f g] :
    Subfunctor.range (pushout.desc a b w ≫ h) =
      Subfunctor.range (a ≫ h) ⊔ Subfunctor.range (b ≫ h) := by
  have e : pushout.desc a b w ≫ h =
      pushout.desc (a ≫ h) (b ≫ h) (by rw [reassoc_of% w]) := by
    apply pushout.hom_ext
    · rw [pushout.inl_desc_assoc, pushout.inl_desc]
    · rw [pushout.inr_desc_assoc, pushout.inr_desc]
  rw [e, range_pushout_desc]

theorem range_coprod_desc_comp (a : X ⟶ W) (b : Y ⟶ W) (h : W ⟶ V) [HasBinaryCoproduct X Y] :
    Subfunctor.range (coprod.desc a b ≫ h) =
      Subfunctor.range (a ≫ h) ⊔ Subfunctor.range (b ≫ h) := by
  rw [coprod.desc_comp, range_coprod_desc]

end CategoryTheory.Subfunctor
