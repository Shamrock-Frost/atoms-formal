import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Saturation
import Atoms.ForMathlib.CategoryTheory.Subfunctor.Union
import Mathlib.Data.Setoid.Basic
import Mathlib.SetTheory.Cardinal.Order

open CategoryTheory Limits MorphismProperty Opposite

namespace Atoms.Homotopical

universe w v

section Quotients

variable {A : Type v} [SmallCategory A]

structure RepresentableCongruence (a : A) : Type v where
  setoid (b : Aᵒᵖ) : Setoid (b.unop ⟶ a)
  rel_comp {b c : Aᵒᵖ} (g : b ⟶ c) {f f' : b.unop ⟶ a} :
    (setoid b).r f f' → (setoid c).r (g.unop ≫ f) (g.unop ≫ f')

def RepresentableCongruence.quotient {a : A} (R : RepresentableCongruence a) :
    Aᵒᵖ ⥤ Type (max w v) where
  obj b := Quotient ((R.setoid b).comap (ULift.down.{w}))
  map g := ↾(Quotient.map (fun f ↦ ULift.up (g.unop ≫ f.down)) (fun _ _ h ↦ R.rel_comp g h))
  map_id b := by
    ext x
    induction x using Quotient.inductionOn
    simp
  map_comp g h := by
    ext x
    induction x using Quotient.inductionOn
    simp

variable {X : Aᵒᵖ ⥤ Type (max w v)}

def kernelCongruence {a : A} (x : X.obj (op a)) : RepresentableCongruence a where
  setoid b := Setoid.ker fun f : b.unop ⟶ a ↦ X.map f.op x
  rel_comp g f f' h := by
    change X.map (g.unop ≫ f).op x = X.map (g.unop ≫ f').op x
    change X.map f.op x = X.map f'.op x at h
    simp only [op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply, h]

def elementMap {a : A} (x : X.obj (op a)) : (kernelCongruence x).quotient ⟶ X where
  app b := ↾(Quotient.lift (fun f : ULift.{w} (b.unop ⟶ a) ↦ X.map f.down.op x)
    (fun _ _ h ↦ h))
  naturality b c g := by
    ext y
    induction y using Quotient.inductionOn with | h f => ?_
    change X.map (g.unop ≫ f.down).op x = X.map g (X.map f.down.op x)
    simp only [op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply]

theorem elementMap_app_injective {a : A} (x : X.obj (op a)) (b : Aᵒᵖ) :
    Function.Injective ((elementMap x).app b) := by
  intro y y' h
  induction y using Quotient.inductionOn
  induction y' using Quotient.inductionOn
  apply Quotient.sound
  exact h

instance mono_elementMap {a : A} (x : X.obj (op a)) : Mono (elementMap x) := by
  rw [NatTrans.mono_iff_mono_app]
  intro b
  rw [mono_iff_injective]
  exact elementMap_app_injective x b

theorem mem_range_elementMap {a : A} (x : X.obj (op a)) :
    x ∈ (Subfunctor.range (elementMap x)).obj (op a) :=
  ⟨Quotient.mk _ (ULift.up (𝟙 a)), by
    change X.map (𝟙 a).op x = x
    simp⟩

end Quotients

section Generators

variable (A : Type v) [SmallCategory A]

structure CellularIndex (A : Type v) [SmallCategory A] : Type (max w v) where
  obj : A
  congruence : RepresentableCongruence obj
  subfunctor : Subfunctor (RepresentableCongruence.quotient.{w} congruence)

def cellularGenerators : MorphismProperty (Aᵒᵖ ⥤ Type (max w v)) :=
  MorphismProperty.ofHoms fun i : CellularIndex.{w, v} A ↦ i.subfunctor.ι

theorem cellularGenerators_le_monomorphisms :
    cellularGenerators.{w, v} A ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) := by
  rintro _ _ _ ⟨i⟩
  exact MorphismProperty.monomorphisms.infer_property _

instance isSmall_cellularGenerators :
    MorphismProperty.IsSmall.{max w v} (cellularGenerators.{w, v} A) :=
  MorphismProperty.isSmall_ofHoms _

theorem cellularGenerators_preimage_ι {X : Aᵒᵖ ⥤ Type (max w v)} {a : A}
    (R : RepresentableCongruence a) (m : R.quotient ⟶ X) (S : Subfunctor X) :
    cellularGenerators A (S.preimage m).ι :=
  MorphismProperty.ofHoms.mk (f := fun i : CellularIndex.{w, v} A ↦ i.subfunctor.ι)
    ⟨a, R, S.preimage m⟩

end Generators

section Union

variable {C : Type v} [SmallCategory C] {X Q : C ⥤ Type (max w v)}

theorem isPushout_preimage_ι (m : Q ⟶ X) [Mono m] (S T : Subfunctor X)
    (hT : S ⊔ Subfunctor.range m = T) :
    IsPushout (S.fromPreimage m) (S.preimage m).ι
      (Subfunctor.homOfLe (hT ▸ le_sup_left)) (Subfunctor.lift m (hT ▸ le_sup_right)) := by
  apply IsPushout.of_forall_isPushout_app
  intro b
  have hm : Function.Injective (m.app b) := (mono_iff_injective _).1 inferInstance
  apply Types.isPushout_of_isPullback_of_mono (k := T.ι.app b) (r' := S.ι.app b)
    (b' := m.app b)
  · rw [Types.isPullback_iff]
    refine ⟨?_, ?_, ?_⟩
    · ext y
      rfl
    · rintro y y' ⟨-, h⟩
      exact Subtype.ext h
    · intro y z h
      exact ⟨⟨z, by simpa [← h] using y.2⟩, Subtype.ext h.symm, rfl⟩
  · ext y
    rfl
  · ext y
    rfl
  · refine Set.eq_univ_of_forall fun ⟨y, hy⟩ ↦ ?_
    simp only [Set.sup_eq_union]
    rw [← hT, Subfunctor.max_obj] at hy
    rcases hy with hy | ⟨z, rfl⟩
    · exact Or.inl ⟨⟨y, hy⟩, rfl⟩
    · exact Or.inr ⟨z, rfl⟩
  · intro y y' _ _ h
    exact hm h

end Union

section UnionChain

variable {C : Type v} [SmallCategory C] {X : C ⥤ Type (max w v)} {ι : Type (max w v)}
  [LinearOrder ι]

def IsUnionChain (R : Subfunctor X) (T : ι → Subfunctor X) (F : WithTop ι → Subfunctor X) :
    Prop :=
  ∀ j : WithTop ι, F j = R ⊔ ⨆ (z : ι) (_ : (z : WithTop ι) < j), T z

namespace IsUnionChain

variable {R : Subfunctor X} {T : ι → Subfunctor X} {F : WithTop ι → Subfunctor X}
  (hF : IsUnionChain R T F)

include hF

theorem left_le (j : WithTop ι) : R ≤ F j := by
  rw [hF j]
  exact le_sup_left

theorem le_of_lt {z : ι} {j : WithTop ι} (h : (z : WithTop ι) < j) : T z ≤ F j := by
  rw [hF j]
  exact le_sup_of_le_right (le_iSup₂_of_le z h le_rfl)

theorem mono : Monotone F := by
  intro j k hjk
  rw [hF j]
  exact sup_le (hF.left_le k) (iSup₂_le fun z hz ↦ hF.le_of_lt (hz.trans_le hjk))

theorem bot [OrderBot (WithTop ι)] : F ⊥ = R := by
  rw [hF ⊥]
  refine le_antisymm (sup_le le_rfl (iSup₂_le fun z hz ↦ ?_)) le_sup_left
  exact absurd hz not_lt_bot

theorem top (h : ⊤ ≤ R ⊔ ⨆ z, T z) : F ⊤ = ⊤ :=
  eq_top_iff.2 (h.trans (sup_le (hF.left_le _)
    (iSup_le fun z ↦ hF.le_of_lt (WithTop.coe_lt_top z))))

theorem succ [SuccOrder (WithTop ι)] (z : ι) :
    F (Order.succ (z : WithTop ι)) = F z ⊔ T z := by
  have hz : ¬IsMax (z : WithTop ι) := not_isMax_of_lt (WithTop.coe_lt_top z)
  apply le_antisymm
  · rw [hF (Order.succ _)]
    refine sup_le ((hF.left_le _).trans le_sup_left) (iSup₂_le fun y hy ↦ ?_)
    rw [Order.lt_succ_iff_of_not_isMax hz] at hy
    rcases hy.lt_or_eq with hy | hy
    · exact (hF.le_of_lt hy).trans le_sup_left
    · obtain rfl := WithTop.coe_injective hy
      exact le_sup_right
  · exact sup_le (hF.mono (Order.le_succ _)) (hF.le_of_lt (Order.lt_succ_of_not_isMax hz))

theorem eq_iSup_of_isSuccLimit [SuccOrder (WithTop ι)] {m : WithTop ι}
    (hm : Order.IsSuccLimit m) : F m = ⨆ k : Set.Iio m, F k := by
  apply le_antisymm
  · obtain ⟨b, hb⟩ := not_isMin_iff.1 hm.not_isMin
    rw [hF m]
    refine sup_le (le_iSup_of_le (f := fun k : Set.Iio m ↦ F k) ⟨b, hb⟩ (hF.left_le b))
      (iSup₂_le fun y hy ↦ ?_)
    refine le_iSup_of_le (⟨Order.succ (y : WithTop ι), hm.succ_lt hy⟩ : Set.Iio m) ?_
    exact hF.le_of_lt (Order.lt_succ_of_not_isMax (not_isMax_of_lt hy))
  · exact iSup_le fun k ↦ hF.mono k.2.le

theorem ι_mem [WellFoundedLT ι] [OrderBot (WithTop ι)] [SuccOrder (WithTop ι)]
    (htop : F ⊤ = ⊤) (W : MorphismProperty (C ⥤ Type (max w v))) [IsSaturated.{max w v} W]
    (hstep : ∀ z : ι, W (Subfunctor.homOfLe (hF.mono (Order.le_succ (z : WithTop ι))))) :
    W R.ι := by
  have hcomp := MorphismProperty.transfiniteCompositionsOfShape_le W _ _
    (Subfunctor.transfiniteCompositionsOfShape_homOfLe W F hF.mono
      (fun _ hm ↦ hF.eq_iSup_of_isSuccLimit hm) fun j hj ↦ by
        induction j using WithTop.recTopCoe with
        | top => exact absurd isMax_top hj
        | coe z => exact hstep z)
  have hf : W (Subfunctor.homOfLe (le_top : R ≤ ⊤)) :=
    (Subfunctor.homOfLe_mem_iff_of_eq W (hF.mono bot_le) le_top hF.bot htop).1 hcomp
  rw [← Subfunctor.homOfLe_ι (le_top : R ≤ ⊤)]
  exact MorphismProperty.comp_mem _ _ _ hf
    (isomorphisms_le_of_containsIdentities _ _ (inferInstance : IsIso (⊤ : Subfunctor X).ι))

end IsUnionChain

end UnionChain

section Chain

variable {A : Type v} [SmallCategory A] {X : Aᵒᵖ ⥤ Type (max w v)}

variable (X) in
def ElementOrder : Type (max w v) := Σ a : A, X.obj (op a)

noncomputable instance : LinearOrder (ElementOrder X) :=
  IsWellOrder.linearOrder WellOrderingRel

instance : WellFoundedLT (ElementOrder X) :=
  ⟨WellOrderingRel.isWellOrder.wf⟩

noncomputable instance : OrderBot (WithTop (ElementOrder X)) :=
  WellFoundedLT.toOrderBot _

noncomputable instance : SuccOrder (WithTop (ElementOrder X)) :=
  SuccOrder.ofLinearWellFoundedLT _

def chain (R : Subfunctor X) (j : WithTop (ElementOrder X)) : Subfunctor X :=
  R ⊔ ⨆ (x : ElementOrder X) (_ : (x : WithTop (ElementOrder X)) < j),
    Subfunctor.range (elementMap x.2)

theorem isUnionChain_chain (R : Subfunctor X) :
    IsUnionChain R (fun x : ElementOrder X ↦ Subfunctor.range (elementMap x.2)) (chain R) :=
  fun _ ↦ rfl

theorem chain_top (R : Subfunctor X) : chain R ⊤ = ⊤ :=
  (isUnionChain_chain R).top fun c y _ ↦
    le_sup_of_le_right (le_iSup (fun x : ElementOrder X ↦ Subfunctor.range (elementMap x.2))
      ⟨c.unop, y⟩) c (mem_range_elementMap (X := X) (a := c.unop) y)

end Chain

section Main

variable (A : Type v) [SmallCategory A]

variable {A} in
theorem saturation_cellularGenerators_ι {X : Aᵒᵖ ⥤ Type (max w v)} (R : Subfunctor X) :
    saturation.{max w v} (cellularGenerators A) R.ι :=
  (isUnionChain_chain R).ι_mem (chain_top R) _ fun x ↦
    MorphismProperty.of_isPushout
      (isPushout_preimage_ι (elementMap x.2) (chain R x) (chain R (Order.succ ↑x))
        ((isUnionChain_chain R).succ x).symm)
      (le_saturation.{max w v} _ _ (cellularGenerators_preimage_ι A _ _ _))

theorem monomorphisms_eq_saturation_cellularGenerators :
    MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type (max w v)) =
      saturation.{max w v} (cellularGenerators A) := by
  refine le_antisymm (fun K X i (hi : Mono i) ↦ ?_)
    (saturation_le _ _ (cellularGenerators_le_monomorphisms A))
  rw [← Subfunctor.toRange_ι i]
  exact MorphismProperty.comp_mem _ _ _
    (isomorphisms_le_of_containsIdentities _ _ (MorphismProperty.isomorphisms.infer_property _))
    (saturation_cellularGenerators_ι _)

instance hasCellularModel : MorphismProperty.HasCellularModel (Aᵒᵖ ⥤ Type (max w v)) where
  cellularModel := cellularGenerators A
  isSmall_cellularModel := isSmall_cellularGenerators A
  saturation_cellularModel := (monomorphisms_eq_saturation_cellularGenerators A).symm

end Main

end Atoms.Homotopical
