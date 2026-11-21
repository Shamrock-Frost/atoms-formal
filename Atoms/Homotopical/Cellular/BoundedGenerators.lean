import Atoms.Homotopical.Cellular.BoundedEmbedding

open CategoryTheory Limits MorphismProperty

namespace Atoms.Homotopical

universe v u

namespace BoundedEmbedding

variable {C : Type u} [Category.{v} C] {B : Type v} [SmallCategory B] (E : BoundedEmbedding C B)

def boundedGenerators (Q : MorphismProperty C) {ι : Type v} (R : ι → C) : MorphismProperty C :=
  MorphismProperty.ofHoms fun t : Σ i, {S : Subfunctor (E.ι.obj (R i)) // Q (E.subι S)} ↦
    E.subι t.2.1

instance isSmall_boundedGenerators (Q : MorphismProperty C) {ι : Type v} (R : ι → C) :
    (E.boundedGenerators Q R).IsSmall.{v} :=
  MorphismProperty.isSmall_ofHoms _

theorem boundedGenerators_le (Q : MorphismProperty C) {ι : Type v} (R : ι → C) :
    E.boundedGenerators Q R ≤ Q := by
  rintro _ _ _ ⟨t⟩
  exact t.2.2

section Chain

variable (D : C → Prop) (Y : C)

def BoundedSubobject : Type v := {Z : Subfunctor (E.ι.obj Y) // D (E.sub Z)}

noncomputable instance : LinearOrder (E.BoundedSubobject D Y) :=
  IsWellOrder.linearOrder WellOrderingRel

instance : WellFoundedLT (E.BoundedSubobject D Y) :=
  ⟨WellOrderingRel.isWellOrder.wf⟩

noncomputable instance : OrderBot (WithTop (E.BoundedSubobject D Y)) :=
  WellFoundedLT.toOrderBot _

noncomputable instance : SuccOrder (WithTop (E.BoundedSubobject D Y)) :=
  SuccOrder.ofLinearWellFoundedLT _

variable (Q : MorphismProperty C) {D Y}

open Classical in
noncomputable def enlargement (V : Subfunctor (E.ι.obj Y)) (z : E.BoundedSubobject D Y) :
    Subfunctor (E.ι.obj Y) :=
  if h : ∃ U : Subfunctor (E.ι.obj Y), z.1 ≤ U ∧ D (E.sub U) ∧
      Q (E.homOfLe (inf_le_right : V ⊓ U ≤ U)) then
    h.choose
  else z.1

theorem le_enlargement (V : Subfunctor (E.ι.obj Y)) (z : E.BoundedSubobject D Y) :
    z.1 ≤ E.enlargement Q V z := by
  unfold enlargement
  split_ifs with h
  · exact h.choose_spec.1
  · exact le_rfl

theorem enlargement_spec (V : Subfunctor (E.ι.obj Y)) (z : E.BoundedSubobject D Y)
    (h : ∃ U : Subfunctor (E.ι.obj Y), z.1 ≤ U ∧ D (E.sub U) ∧
      Q (E.homOfLe (inf_le_right : V ⊓ U ≤ U))) :
    D (E.sub (E.enlargement Q V z)) ∧
      Q (E.homOfLe (inf_le_right : V ⊓ E.enlargement Q V z ≤ E.enlargement Q V z)) := by
  unfold enlargement
  rw [dif_pos h]
  exact h.choose_spec.2

variable (D)

noncomputable def boundedChain (R₀ : Subfunctor (E.ι.obj Y))
    (j : WithTop (E.BoundedSubobject D Y)) : Subfunctor (E.ι.obj Y) :=
  wellFounded_lt.fix (fun j IH ↦ R₀ ⊔ ⨆ (z : E.BoundedSubobject D Y)
    (h : (z : WithTop (E.BoundedSubobject D Y)) < j), E.enlargement Q (IH z h) z) j

theorem isUnionChain_boundedChain (R₀ : Subfunctor (E.ι.obj Y)) :
    IsUnionChain R₀ (fun z : E.BoundedSubobject D Y ↦
      E.enlargement Q (E.boundedChain D Q R₀ z) z) (E.boundedChain D Q R₀) :=
  WellFounded.fix_eq _ _

theorem boundedChain_top (R₀ : Subfunctor (E.ι.obj Y))
    (hcover : ⨆ S : {S : Subfunctor (E.ι.obj Y) // D (E.sub S)}, S.1 = ⊤) :
    E.boundedChain D Q R₀ ⊤ = ⊤ :=
  (E.isUnionChain_boundedChain D Q R₀).top (by
    rw [← hcover]
    refine le_sup_of_le_right (iSup_le fun S ↦ ?_)
    let z : E.BoundedSubobject D Y := S
    exact (E.le_enlargement Q (E.boundedChain D Q R₀ z) z).trans
      (le_iSup (fun z : E.BoundedSubobject D Y ↦
        E.enlargement Q (E.boundedChain D Q R₀ z) z) z))

end Chain

section Steps

variable {Y : C}

theorem saturation_boundedGenerators_subι_of_iso (Q : MorphismProperty C) [IsSaturated.{v} Q]
    {ι : Type v} (R : ι → C) {U : C} {i : ι} (e : U ≅ R i) (P : Subfunctor (E.ι.obj U))
    (hP : Q (E.subι P)) :
    saturation.{v} (E.boundedGenerators Q R) (E.subι P) := by
  let m := E.subι P ≫ e.hom
  have : Mono (E.ι.map m) := by
    rw [Functor.map_comp]
    infer_instance
  let S := Subfunctor.range (E.ι.map m)
  have hiso : ∀ {K L : C} (f : K ≅ L), Q f.hom := fun f ↦
    isomorphisms_le_of_containsIdentities _ _ (Iso.isIso_hom f)
  have hS : E.subι S = (E.isoSubRange m).inv ≫ E.subι P ≫ e.hom := by
    rw [Iso.eq_inv_comp, isoSubRange_hom_subι]
  have hQS : Q (E.subι S) := by
    rw [hS]
    exact MorphismProperty.comp_mem _ _ _ (hiso (E.isoSubRange m).symm)
      (MorphismProperty.comp_mem _ _ _ hP (hiso e))
  have hsat : ∀ {K L : C} (f : K ≅ L), saturation.{v} (E.boundedGenerators Q R) f.hom :=
    fun f ↦ isomorphisms_le_of_containsIdentities _ _ (Iso.isIso_hom f)
  have hPS : E.subι P = (E.isoSubRange m).hom ≫ E.subι S ≫ e.inv := by
    rw [← Category.assoc, isoSubRange_hom_subι, Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [hPS]
  exact MorphismProperty.comp_mem _ _ _ (hsat _)
    (MorphismProperty.comp_mem _ _ _
      (le_saturation.{v} _ _ (MorphismProperty.ofHoms.mk
        (f := fun t : Σ i, {S : Subfunctor (E.ι.obj (R i)) // Q (E.subι S)} ↦ E.subι t.2.1)
        ⟨i, S, hQS⟩))
      (hsat e.symm))

variable (D : C → Prop) (Q : MorphismProperty C)

theorem boundedChain_succ_homOfLe_mem (W : MorphismProperty C) [W.IsStableUnderCobaseChange]
    (R₀ : Subfunctor (E.ι.obj Y)) (z : E.BoundedSubobject D Y)
    (hW : W (E.homOfLe (inf_le_right : E.boundedChain D Q R₀ z ⊓
      E.enlargement Q (E.boundedChain D Q R₀ z) z ≤ E.enlargement Q (E.boundedChain D Q R₀ z) z))) :
    W (E.homOfLe ((E.isUnionChain_boundedChain D Q R₀).mono
      (Order.le_succ (z : WithTop (E.BoundedSubobject D Y))))) := by
  have hT := (E.isUnionChain_boundedChain D Q R₀).succ z
  refine (E.homOfLe_mem_iff_of_eq W _ (le_sup_left : E.boundedChain D Q R₀ z ≤
    E.boundedChain D Q R₀ z ⊔ E.enlargement Q (E.boundedChain D Q R₀ z) z) rfl hT).2 ?_
  exact MorphismProperty.of_isPushout (E.isPushout_homOfLe ⟨rfl, rfl⟩) hW

end Steps

section Main

variable {Y : C} (D : C → Prop) (Q : MorphismProperty C)

theorem boundedChain_succ_homOfLe_mem_of_subι_mem [IsSaturated.{v} Q]
    (henlarge : ∀ {X Y : C} (i : X ⟶ Y), Q i → ∀ Z : Subfunctor (E.ι.obj Y), D (E.sub Z) →
      ∃ U : Subfunctor (E.ι.obj Y), Z ≤ U ∧ D (E.sub U) ∧
        Q (E.homOfLe (inf_le_right : Subfunctor.range (E.ι.map i) ⊓ U ≤ U)))
    (R₀ : Subfunctor (E.ι.obj Y)) (z : E.BoundedSubobject D Y)
    (hz : Q (E.subι (E.boundedChain D Q R₀ z))) :
    Q (E.homOfLe ((E.isUnionChain_boundedChain D Q R₀).mono
      (Order.le_succ (z : WithTop (E.BoundedSubobject D Y))))) := by
  obtain ⟨U, hzU, hU, hQU⟩ := henlarge _ hz z.1 z.2
  refine E.boundedChain_succ_homOfLe_mem D Q Q R₀ z (E.enlargement_spec Q _ z
    ⟨U, hzU, hU, (E.homOfLe_mem_iff_of_eq Q _ _ ?_ rfl).1 hQU⟩).2
  rw [range_map_subι]

theorem boundedChain_subι_mem [IsSaturated.{v} Q]
    (hcancel : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), Mono f → Mono g → Q f →
      Q (f ≫ g) → Q g)
    (henlarge : ∀ {X Y : C} (i : X ⟶ Y), Q i → ∀ Z : Subfunctor (E.ι.obj Y), D (E.sub Z) →
      ∃ U : Subfunctor (E.ι.obj Y), Z ≤ U ∧ D (E.sub U) ∧
        Q (E.homOfLe (inf_le_right : Subfunctor.range (E.ι.map i) ⊓ U ≤ U)))
    (R₀ : Subfunctor (E.ι.obj Y)) (hR₀ : Q (E.subι R₀)) (j : WithTop (E.BoundedSubobject D Y)) :
    Q (E.subι (E.boundedChain D Q R₀ j)) := by
  induction j using WellFoundedLT.induction with
  | ind j IH =>
  let G : WithTop (E.BoundedSubobject D Y) → Subfunctor (E.ι.obj Y) :=
    fun k ↦ E.boundedChain D Q R₀ (min k j)
  have hF := E.isUnionChain_boundedChain D Q R₀
  have hG : Monotone G := fun k k' h ↦ hF.mono (min_le_min_right j h)
  have hlim : ∀ m, Order.IsSuccLimit m → G m = ⨆ k : Set.Iio m, G k := by
    intro m hm
    rcases le_or_gt m j with hmj | hjm
    · simp only [G, min_eq_left hmj]
      rw [hF.eq_iSup_of_isSuccLimit hm]
      exact iSup_congr fun k ↦ by rw [min_eq_left (k.2.le.trans hmj)]
    · refine le_antisymm (le_iSup_of_le ⟨j, hjm⟩ (hF.mono ?_))
        (iSup_le fun k ↦ hG k.2.le)
      rw [min_eq_right hjm.le, min_self]
  have hstep : ∀ k, ¬IsMax k → Q (E.homOfLe (hG (Order.le_succ k))) := by
    intro k hk
    rcases lt_or_ge k j with hkj | hjk
    · induction k using WithTop.recTopCoe with
      | top => exact absurd hkj not_top_lt
      | coe z =>
        refine (E.homOfLe_mem_iff_of_eq Q _ _ (by simp only [G, min_eq_left hkj.le])
          (by simp only [G, min_eq_left (Order.succ_le_of_lt hkj)])).2
          (E.boundedChain_succ_homOfLe_mem_of_subι_mem D Q henlarge R₀ z (IH _ hkj))
    · refine E.homOfLe_mem_of_eq Q _ ?_
      simp only [G, min_eq_right hjk, min_eq_right (hjk.trans (Order.le_succ k))]
  have hcomp := MorphismProperty.transfiniteCompositionsOfShape_le Q _ _
    (E.transfiniteCompositionsOfShape_homOfLe Q G hG hlim hstep)
  have hf : Q (E.homOfLe (hF.left_le j)) :=
    (E.homOfLe_mem_iff_of_eq Q _ _ (by simp only [G, bot_le, min_eq_left, hF.bot])
      (by simp only [G, le_top, min_eq_right])).2 hcomp
  exact hcancel _ _ inferInstance inferInstance hf (by rw [homOfLe_subι]; exact hR₀)

theorem saturation_boundedGenerators_subι [IsSaturated.{v} Q]
    (hcancel : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), Mono f → Mono g → Q f →
      Q (f ≫ g) → Q g)
    {ι : Type v} (R : ι → C) (hrep : ∀ X : C, D X → ∃ i, Nonempty (X ≅ R i))
    (hcover : ∀ X : C, ⨆ S : {S : Subfunctor (E.ι.obj X) // D (E.sub S)}, S.1 = ⊤)
    (henlarge : ∀ {X Y : C} (i : X ⟶ Y), Q i → ∀ Z : Subfunctor (E.ι.obj Y), D (E.sub Z) →
      ∃ U : Subfunctor (E.ι.obj Y), Z ≤ U ∧ D (E.sub U) ∧
        Q (E.homOfLe (inf_le_right : Subfunctor.range (E.ι.map i) ⊓ U ≤ U)))
    (R₀ : Subfunctor (E.ι.obj Y)) (hR₀ : Q (E.subι R₀)) :
    saturation.{v} (E.boundedGenerators Q R) (E.subι R₀) := by
  refine E.subι_mem_of_isUnionChain (E.isUnionChain_boundedChain D Q R₀)
    (E.boundedChain_top D Q R₀ (hcover Y)) _ fun z ↦ ?_
  have hz := E.boundedChain_subι_mem D Q hcancel henlarge R₀ hR₀ z
  obtain ⟨U, hzU, hU, hQU⟩ := henlarge _ hz z.1 z.2
  have h := E.enlargement_spec Q _ z
    ⟨U, hzU, hU, (E.homOfLe_mem_iff_of_eq Q _ _ (by rw [range_map_subι]) rfl).1 hQU⟩
  obtain ⟨i, ⟨e⟩⟩ := hrep _ h.1
  refine E.boundedChain_succ_homOfLe_mem D Q _ R₀ z ?_
  let k := E.homOfLe (inf_le_right : E.boundedChain D Q R₀ z ⊓
    E.enlargement Q (E.boundedChain D Q R₀ z) z ≤ E.enlargement Q (E.boundedChain D Q R₀ z) z)
  have hiso : ∀ {K L : C} (f : K ≅ L), Q f.hom := fun f ↦
    isomorphisms_le_of_containsIdentities _ _ (Iso.isIso_hom f)
  have hk : k = (E.isoSubRange k).hom ≫ E.subι _ := (isoSubRange_hom_subι _ _).symm
  have hP : Q (E.subι (Subfunctor.range (E.ι.map k))) := by
    rw [← Iso.inv_hom_id_assoc (E.isoSubRange k) (E.subι _), ← hk]
    exact MorphismProperty.comp_mem _ _ _ (hiso (E.isoSubRange k).symm) h.2
  have hs := MorphismProperty.comp_mem _ _ _
    (isomorphisms_le_of_containsIdentities _ _ (Iso.isIso_hom (E.isoSubRange k)))
    (E.saturation_boundedGenerators_subι_of_iso Q R e _ hP)
  rw [← hk] at hs
  exact hs

theorem eq_saturation_boundedGenerators [IsSaturated.{v} Q] (hQ : Q ≤ monomorphisms C)
    (hcancel : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), Mono f → Mono g → Q f →
      Q (f ≫ g) → Q g)
    {ι : Type v} (R : ι → C) (hrep : ∀ X : C, D X → ∃ i, Nonempty (X ≅ R i))
    (hcover : ∀ X : C, ⨆ S : {S : Subfunctor (E.ι.obj X) // D (E.sub S)}, S.1 = ⊤)
    (henlarge : ∀ {X Y : C} (i : X ⟶ Y), Q i → ∀ Z : Subfunctor (E.ι.obj Y), D (E.sub Z) →
      ∃ U : Subfunctor (E.ι.obj Y), Z ≤ U ∧ D (E.sub U) ∧
        Q (E.homOfLe (inf_le_right : Subfunctor.range (E.ι.map i) ⊓ U ≤ U))) :
    Q = saturation.{v} (E.boundedGenerators Q R) := by
  refine le_antisymm (fun K Y i hi ↦ ?_) (saturation_le _ _ (E.boundedGenerators_le Q R))
  have : Mono i := hQ _ hi
  have hiso : ∀ {K L : C} (f : K ≅ L), Q f.hom := fun f ↦
    isomorphisms_le_of_containsIdentities _ _ (Iso.isIso_hom f)
  have hr : Q (E.subι (Subfunctor.range (E.ι.map i))) :=
    hcancel _ _ inferInstance inferInstance (hiso (E.isoSubRange i))
      (by rw [isoSubRange_hom_subι]; exact hi)
  rw [← E.isoSubRange_hom_subι i]
  exact MorphismProperty.comp_mem _ _ _
    (isomorphisms_le_of_containsIdentities _ _ (Iso.isIso_hom _))
    (E.saturation_boundedGenerators_subι D Q hcancel R hrep hcover henlarge _ hr)

end Main

end BoundedEmbedding

section Presheaves

variable {A : Type v} [SmallCategory A]

abbrev boundedGenerators (Q : MorphismProperty (Aᵒᵖ ⥤ Type v)) {ι : Type v}
    (R : ι → Aᵒᵖ ⥤ Type v) : MorphismProperty (Aᵒᵖ ⥤ Type v) :=
  (BoundedEmbedding.id A).boundedGenerators Q R

instance isSmall_boundedGenerators (Q : MorphismProperty (Aᵒᵖ ⥤ Type v)) {ι : Type v}
    (R : ι → Aᵒᵖ ⥤ Type v) : (boundedGenerators Q R).IsSmall.{v} :=
  (BoundedEmbedding.id A).isSmall_boundedGenerators Q R

theorem boundedGenerators_le (Q : MorphismProperty (Aᵒᵖ ⥤ Type v)) {ι : Type v}
    (R : ι → Aᵒᵖ ⥤ Type v) : boundedGenerators Q R ≤ Q :=
  (BoundedEmbedding.id A).boundedGenerators_le Q R

theorem eq_saturation_boundedGenerators (Q : MorphismProperty (Aᵒᵖ ⥤ Type v))
    [IsSaturated.{v} Q] (hQ : Q ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v))
    (hcancel : ∀ {X Y Z : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y) (g : Y ⟶ Z), Mono f → Mono g → Q f →
      Q (f ≫ g) → Q g)
    (D : (Aᵒᵖ ⥤ Type v) → Prop) {ι : Type v} (R : ι → Aᵒᵖ ⥤ Type v)
    (hrep : ∀ X : Aᵒᵖ ⥤ Type v, D X → ∃ i, Nonempty (X ≅ R i))
    (hcover : ∀ X : Aᵒᵖ ⥤ Type v, ⨆ S : {S : Subfunctor X // D S.toFunctor}, S.1 = ⊤)
    (henlarge : ∀ {X Y : Aᵒᵖ ⥤ Type v} (i : X ⟶ Y), Q i → ∀ Z : Subfunctor Y, D Z.toFunctor →
      ∃ U : Subfunctor Y, Z ≤ U ∧ D U.toFunctor ∧
        Q (Subfunctor.homOfLe (inf_le_right : Subfunctor.range i ⊓ U ≤ U))) :
    Q = saturation.{v} (boundedGenerators Q R) :=
  (BoundedEmbedding.id A).eq_saturation_boundedGenerators D Q hQ hcancel R hrep hcover
    @fun _ Y i hi Z hZ => by
      obtain ⟨U, hZU, hU, hQU⟩ := henlarge i hi Z hZ
      exact ⟨U, hZU, hU, (congrArg (fun f => Q f)
        (BoundedEmbedding.id_homOfLe (Y := Y) (inf_le_right : Subfunctor.range i ⊓ U ≤ U))).mpr
        hQU⟩

end Presheaves

end Atoms.Homotopical
