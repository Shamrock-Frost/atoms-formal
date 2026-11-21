import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Saturation
import Mathlib.CategoryTheory.Monoidal.PushoutProduct

namespace CategoryTheory

open Limits MorphismProperty

universe w v u

namespace Limits

variable {C : Type u} [Category.{v} C] {J : Type*} [Category* J] {Φ : J ⥤ C} (c : Cocone Φ)

@[simps]
def coconeArrows : J ⥤ Arrow C where
  obj j := Arrow.mk (c.ι.app j)
  map φ := Arrow.homMk (Φ.map φ) (𝟙 c.pt) (by simp)

@[simps]
def coconeArrowsCocone : Cocone (coconeArrows c) where
  pt := Arrow.mk (𝟙 c.pt)
  ι :=
    { app j := Arrow.homMk (c.ι.app j) (𝟙 c.pt) rfl
      naturality _ _ φ := by
        ext
        · exact (c.w φ).trans (Category.comp_id _).symm
        · exact (Category.comp_id _).trans (Category.id_comp _).symm }

noncomputable def isColimitCoconeArrowsCocone [IsConnected J] (hc : IsColimit c) :
    IsColimit (coconeArrowsCocone c) :=
  Comma.fstSndJointlyReflectColimit hc (isColimitConstCocone J c.pt)

theorem isWellOrderContinuous_coconeArrows_comp_of_isConnected {J : Type w} [LinearOrder J]
    {Φ : J ⥤ C} [Φ.IsWellOrderContinuous] (c : Cocone Φ) {D : Type*} [Category* D]
    (B : Arrow C ⥤ D)
    (hB : ∀ m : J, IsConnected (Set.Iio m) → PreservesColimitsOfShape (Set.Iio m) B) :
    (coconeArrows c ⋙ B).IsWellOrderContinuous where
  nonempty_isColimit m hm := by
    obtain ⟨j, hj⟩ := not_isMin_iff.1 hm.not_isMin
    have : Nonempty (Set.Iio m) := ⟨⟨j, hj⟩⟩
    have := hB m (IsFiltered.isConnected _)
    exact ⟨isColimitOfPreserves B (Comma.fstSndJointlyReflectColimit
      (c := (Set.principalSegIio m).cocone (coconeArrows c))
      (Φ.isColimitOfIsWellOrderContinuous m hm) (isColimitConstCocone (Set.Iio m) c.pt))⟩

theorem isWellOrderContinuous_coconeArrows_comp {J : Type w} [LinearOrder J] {Φ : J ⥤ C}
    [Φ.IsWellOrderContinuous] (c : Cocone Φ) {D : Type*} [Category* D] (B : Arrow C ⥤ D)
    [∀ m : J, PreservesColimitsOfShape (Set.Iio m) B] :
    (coconeArrows c ⋙ B).IsWellOrderContinuous :=
  isWellOrderContinuous_coconeArrows_comp_of_isConnected c B fun _ _ ↦ inferInstance

end Limits

namespace NatTrans

variable {C : Type u} [Category.{v} C] [HasPushouts C] {F G : C ⥤ C} (α : F ⟶ G)

noncomputable abbrev leibnizSource {K X : C} (i : K ⟶ X) : C :=
  pushout (α.app K) (F.map i)

noncomputable def leibnizBox {K X : C} (i : K ⟶ X) : leibnizSource α i ⟶ G.obj X :=
  pushout.desc (G.map i) (α.app X) (α.naturality i).symm

@[reassoc (attr := simp)]
theorem inl_leibnizBox {K X : C} (i : K ⟶ X) :
    pushout.inl (α.app K) (F.map i) ≫ leibnizBox α i = G.map i :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem inr_leibnizBox {K X : C} (i : K ⟶ X) :
    pushout.inr (α.app K) (F.map i) ≫ leibnizBox α i = α.app X :=
  pushout.inr_desc _ _ _

noncomputable def leibnizSourceMap {K X K' X' : C} {i : K ⟶ X} {i' : K' ⟶ X'} (t : K ⟶ K')
    (s : X ⟶ X') (w : t ≫ i' = i ≫ s) : leibnizSource α i ⟶ leibnizSource α i' :=
  pushout.desc (G.map t ≫ pushout.inl _ _) (F.map s ≫ pushout.inr _ _) (by
    rw [← α.naturality_assoc, pushout.condition, ← F.map_comp_assoc, w, F.map_comp_assoc])

@[reassoc (attr := simp)]
theorem inl_leibnizSourceMap {K X K' X' : C} {i : K ⟶ X} {i' : K' ⟶ X'} (t : K ⟶ K')
    (s : X ⟶ X') (w : t ≫ i' = i ≫ s) :
    pushout.inl _ _ ≫ leibnizSourceMap α t s w = G.map t ≫ pushout.inl _ _ :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem inr_leibnizSourceMap {K X K' X' : C} {i : K ⟶ X} {i' : K' ⟶ X'} (t : K ⟶ K')
    (s : X ⟶ X') (w : t ≫ i' = i ≫ s) :
    pushout.inr _ _ ≫ leibnizSourceMap α t s w = F.map s ≫ pushout.inr _ _ :=
  pushout.inr_desc _ _ _

@[reassoc (attr := simp)]
theorem leibnizSourceMap_leibnizBox {K X K' X' : C} {i : K ⟶ X} {i' : K' ⟶ X'} (t : K ⟶ K')
    (s : X ⟶ X') (w : t ≫ i' = i ≫ s) :
    leibnizSourceMap α t s w ≫ leibnizBox α i' = leibnizBox α i ≫ G.map s := by
  refine pushout.hom_ext ?_ ?_
  · rw [inl_leibnizSourceMap_assoc, inl_leibnizBox, inl_leibnizBox_assoc, ← G.map_comp,
      ← G.map_comp, w]
  · rw [inr_leibnizSourceMap_assoc, inr_leibnizBox, inr_leibnizBox_assoc]
    exact α.naturality s

@[simps]
noncomputable def leibnizArrow : Arrow C ⥤ Arrow C where
  obj f := Arrow.mk (leibnizBox α f.hom)
  map {f f'} sq := Arrow.homMk (leibnizSourceMap α sq.left sq.right sq.w)
    (G.map sq.right) (leibnizSourceMap_leibnizBox α _ _ _)
  map_id f := by
    ext
    · refine pushout.hom_ext ?_ ?_ <;> simp
    · simp
  map_comp _ _ := by
    ext
    · refine pushout.hom_ext ?_ ?_ <;> simp
    · simp

def leibnizPreimage (P : MorphismProperty C) : MorphismProperty C :=
  fun _ _ i ↦ P (leibnizBox α i)

theorem isIso_leibnizBox {K X : C} (i : K ⟶ X) [IsIso i] : IsIso (leibnizBox α i) := by
  have : IsIso (pushout.inl (α.app K) (F.map i) ≫ leibnizBox α i) := by
    rw [inl_leibnizBox]; infer_instance
  exact IsIso.of_isIso_comp_left (pushout.inl (α.app K) (F.map i)) _

theorem isPushout_leibnizBox [PreservesColimitsOfShape WalkingSpan F]
    [PreservesColimitsOfShape WalkingSpan G] {K X K' X' : C} {t : K ⟶ K'} {i : K ⟶ X}
    {i' : K' ⟶ X'} {s : X ⟶ X'} (sq : IsPushout t i i' s) :
    IsPushout (leibnizSourceMap α t s sq.w) (leibnizBox α i) (leibnizBox α i')
      (G.map s) := by
  have hF := F.map_isPushout sq
  have hG := G.map_isPushout sq.flip
  have outer : IsPushout (α.app K ≫ G.map t) (F.map i) (pushout.inl _ _)
      (pushout.inr (α.app K) (F.map i) ≫ leibnizSourceMap α t s sq.w) := by
    rw [← α.naturality t, inr_leibnizSourceMap]
    exact hF.paste_horiz (IsPushout.of_hasPushout (α.app K') (F.map i'))
  have left : IsPushout (G.map t) (pushout.inl _ _) (pushout.inl _ _)
      (leibnizSourceMap α t s sq.w) :=
    ((IsPushout.of_hasPushout (α.app K) (F.map i)).paste_horiz_iff (by simp)).1 outer
  refine (left.flip.paste_horiz_iff (by simp)).1 ?_ |>.flip
  simpa using hG

theorem isPushout_leibnizSourceMap_of_comp {K K' Y : C} (u : K ⟶ K') (a : K ⟶ Y)
    (b : K' ⟶ Y) (w : u ≫ b = a ≫ 𝟙 Y) :
    IsPushout (leibnizSourceMap α (𝟙 K) b (by simpa using w.symm)) (leibnizBox α u)
      (leibnizSourceMap α u (𝟙 Y) w) (pushout.inl (α.app K') (F.map b)) := by
  obtain rfl : a = u ≫ b := by simpa using w.symm
  have right : IsPushout (F.map b) (pushout.inr _ _) (pushout.inr _ _)
      (leibnizSourceMap α (i := u) (i' := u ≫ b) (𝟙 K) b (by simp)) := by
    refine ((IsPushout.of_hasPushout (α.app K) (F.map u)).flip.paste_horiz_iff
      (by simp)).1 ?_
    convert (IsPushout.of_hasPushout (α.app K) (F.map (u ≫ b))).flip using 1 <;> simp
  refine (right.paste_vert_iff ?_).1 ?_
  · refine pushout.hom_ext ?_ ?_
    · simp
    · simp [pushout.condition]
  · convert (IsPushout.of_hasPushout (α.app K') (F.map b)).flip using 1 <;> simp

section Closure

variable (P : MorphismProperty C)

theorem isStableUnderCobaseChange_leibnizPreimage [PreservesColimitsOfShape WalkingSpan F]
    [PreservesColimitsOfShape WalkingSpan G] [P.IsStableUnderCobaseChange] :
    (leibnizPreimage α P).IsStableUnderCobaseChange where
  of_isPushout sq hf :=
    IsStableUnderCobaseChange.of_isPushout (P := P) (isPushout_leibnizBox α sq) hf

theorem isStableUnderRetracts_leibnizPreimage [P.IsStableUnderRetracts] :
    (leibnizPreimage α P).IsStableUnderRetracts where
  of_retract h hg := P.of_retract (Retract.map h (leibnizArrow α)) hg

end Closure

@[simps]
def leibnizSpan : Arrow C ⥤ (WalkingSpan ⥤ C) where
  obj f := span (α.app f.left) (F.map f.hom)
  map sq := spanHomMk (F.map sq.left) (G.map sq.left) (F.map sq.right)
    (by dsimp; exact (α.naturality sq.left).symm)
    (by dsimp; simp only [← F.map_comp, sq.w])
  map_id f := by ext (_ | _ | _) <;> dsimp [spanHomMk] <;> simp
  map_comp _ _ := by ext (_ | _ | _) <;> dsimp [spanHomMk] <;> simp

noncomputable def leibnizSourceIsoColim :
    leibnizArrow α ⋙ Arrow.leftFunc ≅ leibnizSpan α ⋙ colim :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun sq ↦ by
    refine pushout.hom_ext ?_ ?_
    · exact (congrArg (pushout.inl _ _ ≫ ·) (Category.comp_id _)).trans
        ((inl_leibnizSourceMap α _ _ sq.w).trans
          ((colimit.ι_map ((leibnizSpan α).map sq) WalkingSpan.left).symm.trans
            (congrArg (pushout.inl _ _ ≫ ·) (Category.id_comp _)).symm))
    · exact (congrArg (pushout.inr _ _ ≫ ·) (Category.comp_id _)).trans
        ((inr_leibnizSourceMap α _ _ sq.w).trans
          ((colimit.ι_map ((leibnizSpan α).map sq) WalkingSpan.right).symm.trans
            (congrArg (pushout.inr _ _ ≫ ·) (Category.id_comp _)).symm))

omit [HasPushouts C] in
theorem preservesColimitsOfShape_leibnizSpan (K : Type*) [Category* K] [HasColimitsOfShape K C]
    [PreservesColimitsOfShape K F] [PreservesColimitsOfShape K G] :
    PreservesColimitsOfShape K (leibnizSpan α) := by
  refine preservesColimitsOfShape_of_evaluation _ _ fun k ↦ ?_
  rcases k with _ | _ | _
  · exact preservesColimitsOfShape_of_natIso (F := Arrow.leftFunc ⋙ F)
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦
        (Category.comp_id _).trans (Category.id_comp (F.map f.left)).symm)
  · exact preservesColimitsOfShape_of_natIso (F := Arrow.leftFunc ⋙ G)
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦
        (Category.comp_id _).trans (Category.id_comp (G.map f.left)).symm)
  · exact preservesColimitsOfShape_of_natIso (F := Arrow.rightFunc ⋙ F)
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) fun f ↦
        (Category.comp_id _).trans (Category.id_comp (F.map f.right)).symm)

theorem preservesColimitsOfShape_leibnizSource (K : Type*) [Category* K]
    [HasColimitsOfShape K C] [PreservesColimitsOfShape K F] [PreservesColimitsOfShape K G] :
    PreservesColimitsOfShape K (leibnizArrow α ⋙ Arrow.leftFunc) := by
  have := preservesColimitsOfShape_leibnizSpan α K
  exact preservesColimitsOfShape_of_natIso (leibnizSourceIsoColim α).symm

theorem leibnizBox_mem_of_transfiniteCompositionOfShape_of_isConnected
    [HasColimitsOfSize.{w, w} C]
    [hF : ∀ (K : Type w) [SmallCategory K] [IsConnected K], PreservesColimitsOfShape K F]
    [hG : ∀ (K : Type w) [SmallCategory K] [IsConnected K], PreservesColimitsOfShape K G]
    (P : MorphismProperty C) [IsSaturated.{w} P]
    (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] {X Y : C}
    {f : X ⟶ Y} (h : (leibnizPreimage α P).TransfiniteCompositionOfShape J f) :
    P (leibnizBox α f) := by
  let c : Cocone h.F := Cocone.mk Y h.incl
  let B := leibnizArrow α ⋙ Arrow.leftFunc
  have (K : Type w) [SmallCategory K] [IsConnected K] : PreservesColimitsOfShape K B :=
    preservesColimitsOfShape_leibnizSource α K
  have := isWellOrderContinuous_coconeArrows_comp_of_isConnected c B fun _ _ ↦ inferInstance
  have : IsConnected J := IsFiltered.isConnected J
  let incl : coconeArrows c ⋙ B ⟶ (Functor.const J).obj (G.obj Y) :=
    { app j := leibnizBox α (h.incl.app j)
      naturality _ _ φ :=
        (leibnizSourceMap_leibnizBox α (h.F.map φ) (𝟙 Y) (h.incl.naturality φ)).trans
          (by rw [G.map_id]; rfl) }
  let tc : P.TransfiniteCompositionOfShape J (leibnizBox α (h.incl.app ⊥)) :=
    { F := coconeArrows c ⋙ B
      isoBot := Iso.refl _
      incl := incl
      isColimit := IsColimit.ofIsoColimit
        (isColimitOfPreserves B (isColimitCoconeArrowsCocone c h.isColimit))
        (Cocone.ext (@asIso _ _ _ _ (leibnizBox α (𝟙 Y)) (isIso_leibnizBox α (𝟙 Y))) fun j ↦
          (leibnizSourceMap_leibnizBox α (h.incl.app j) (𝟙 Y) rfl).trans
            (by rw [G.map_id, Category.comp_id]))
      fac := Category.id_comp _
      map_mem j hj := IsStableUnderCobaseChange.of_isPushout (P := P)
        (isPushout_leibnizSourceMap_of_comp α _ (h.incl.app j) (h.incl.app (Order.succ j))
          (h.incl.naturality _)) (h.map_mem j hj) }
  have hg := P.transfiniteCompositionsOfShape_le J _ tc.mem
  have e : Arrow.mk (leibnizBox α (h.incl.app ⊥)) ≅ Arrow.mk (leibnizBox α f) :=
    (leibnizArrow α).mapIso (Arrow.isoMk (f := Arrow.mk (h.incl.app ⊥)) (g := Arrow.mk f)
      h.isoBot (Iso.refl Y) (by
        dsimp; rw [Category.comp_id]; exact (Iso.eq_inv_comp h.isoBot).1 h.fac.symm))
  exact (P.arrow_mk_iso_iff e).1 hg

theorem leibnizBox_mem_of_transfiniteCompositionOfShape [HasColimitsOfSize.{w, w} C]
    [PreservesColimitsOfSize.{w, w} F] [PreservesColimitsOfSize.{w, w} G]
    (P : MorphismProperty C) [IsSaturated.{w} P]
    (J : Type w) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] {X Y : C}
    {f : X ⟶ Y} (h : (leibnizPreimage α P).TransfiniteCompositionOfShape J f) :
    P (leibnizBox α f) :=
  leibnizBox_mem_of_transfiniteCompositionOfShape_of_isConnected α P J h
    (hF := fun _ _ _ ↦ inferInstance) (hG := fun _ _ _ ↦ inferInstance)

theorem isSaturated_leibnizPreimage_of_isConnected [HasColimitsOfSize.{w, w} C]
    [hF : ∀ (K : Type w) [SmallCategory K] [IsConnected K], PreservesColimitsOfShape K F]
    [hG : ∀ (K : Type w) [SmallCategory K] [IsConnected K], PreservesColimitsOfShape K G]
    [PreservesColimitsOfShape WalkingSpan F] [PreservesColimitsOfShape WalkingSpan G]
    (P : MorphismProperty C) [IsSaturated.{w} P] :
    IsSaturated.{w} (leibnizPreimage α P) where
  isStableUnderCobaseChange := isStableUnderCobaseChange_leibnizPreimage α P
  isStableUnderRetracts := isStableUnderRetracts_leibnizPreimage α P
  isStableUnderTransfiniteComposition :=
    ⟨fun J _ _ _ _ ↦ ⟨fun _ _ _ ⟨h⟩ ↦
      leibnizBox_mem_of_transfiniteCompositionOfShape_of_isConnected α P J h
        (hF := hF) (hG := hG)⟩⟩

theorem isSaturated_leibnizPreimage [HasColimitsOfSize.{w, w} C]
    [PreservesColimitsOfSize.{w, w} F] [PreservesColimitsOfSize.{w, w} G]
    [PreservesColimitsOfShape WalkingSpan F] [PreservesColimitsOfShape WalkingSpan G]
    (P : MorphismProperty C) [IsSaturated.{w} P] :
    IsSaturated.{w} (leibnizPreimage α P) :=
  isSaturated_leibnizPreimage_of_isConnected α P
    (hF := fun _ _ _ ↦ inferInstance) (hG := fun _ _ _ ↦ inferInstance)

end NatTrans

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] [HasPushouts C]

theorem pushoutObjObj_ι_mem_of_saturation [HasColimitsOfSize.{w, w} C] (B : C ⥤ C ⥤ C)
    [∀ X, PreservesColimitsOfShape WalkingSpan (B.obj X)]
    [∀ Y, PreservesColimitsOfShape WalkingSpan (B.flip.obj Y)]
    [hB : ∀ X (K : Type w) [SmallCategory K] [IsConnected K],
      PreservesColimitsOfShape K (B.obj X)]
    [hB' : ∀ Y (K : Type w) [SmallCategory K] [IsConnected K],
      PreservesColimitsOfShape K (B.flip.obj Y)]
    (P S₁ S₂ : MorphismProperty C) [IsSaturated.{w} P]
    (h : ∀ ⦃X₁ Y₁ X₂ Y₂ : C⦄ (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂), S₁ f₁ → S₂ f₂ →
      P (Functor.PushoutObjObj.ofHasPushout B f₁ f₂).ι)
    {X₁ Y₁ X₂ Y₂ : C} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    (h₁ : saturation.{w} S₁ f₁) (h₂ : saturation.{w} S₂ f₂) :
    P (Functor.PushoutObjObj.ofHasPushout B f₁ f₂).ι := by
  have hswap {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
      P (Functor.PushoutObjObj.ofHasPushout B.flip f₂ f₁).ι ↔
        P (Functor.PushoutObjObj.ofHasPushout B f₁ f₂).ι :=
    P.arrow_mk_iso_iff (Functor.PushoutObjObj.ι_iso_of_iso_left (f₁ := Arrow.mk f₂)
      (f₂ := Arrow.mk f₁) (.ofHasPushout B.flip f₂ f₁)
      (Functor.PushoutObjObj.ofHasPushout B f₁ f₂).flip (Iso.refl _))
  have h₁' {X₁ Y₁ : C} (f₁ : X₁ ⟶ Y₁) (hf₁ : S₁ f₁) :
      saturation.{w} S₂ ≤ NatTrans.leibnizPreimage (B.map f₁) P :=
    have := NatTrans.isSaturated_leibnizPreimage_of_isConnected (B.map f₁) P
      (hF := fun _ _ _ ↦ inferInstance) (hG := fun _ _ _ ↦ inferInstance)
    saturation_le _ _ fun _ _ f₂ hf₂ ↦ h f₁ f₂ hf₁ hf₂
  have := NatTrans.isSaturated_leibnizPreimage_of_isConnected (B.flip.map f₂) P
    (hF := fun _ _ _ ↦ inferInstance) (hG := fun _ _ _ ↦ inferInstance)
  exact (hswap f₁ f₂).1 (saturation_le S₁ (NatTrans.leibnizPreimage (B.flip.map f₂) P)
    (fun _ _ f₁ hf₁ ↦ (hswap f₁ f₂).2 (h₁' f₁ hf₁ f₂ h₂)) f₁ h₁)

end MorphismProperty

section Monoidal

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPushouts C]

open MonoidalCategory.Arrow in
noncomputable def NatTrans.leibnizBoxArrowIso {F G : C ⥤ C} (α : F ⟶ G) {A B : C} (e : A ⟶ B)
    (φF : F ≅ tensorLeft A) (φG : G ≅ tensorLeft B)
    (h : ∀ X, α.app X ≫ φG.hom.app X = φF.hom.app X ≫ e ▷ X) {K X : C} (i : K ⟶ X) :
    Arrow.mk (NatTrans.leibnizBox α i) ≅ (Arrow.mk e □ Arrow.mk i) :=
  have hp : IsPushout (α.app K) (F.map i) (φG.hom.app K ≫ pushout.inl _ _)
      (φF.hom.app X ≫ pushout.inr _ _) :=
    (IsPushout.of_hasPushout (e ▷ K) (A ◁ i)).of_iso (φF.app K).symm (φG.app K).symm
      (φF.app X).symm (Iso.refl _) (by
        rw [← cancel_epi (φF.hom.app K)]
        simp [← reassoc_of% (h K)]) (φF.inv.naturality i) (by simp) (by simp)
  have hw : hp.isoPushout.inv ≫ pushout.desc (B ◁ i) (e ▷ X) (whisker_exchange e i).symm =
      NatTrans.leibnizBox α i ≫ φG.hom.app X := by
    refine pushout.hom_ext ?_ ?_
    · rw [← Category.assoc, IsPushout.inl_isoPushout_inv, Category.assoc, pushout.inl_desc,
        NatTrans.inl_leibnizBox_assoc]
      exact (φG.hom.naturality i).symm
    · rw [← Category.assoc, IsPushout.inr_isoPushout_inv, Category.assoc, pushout.inr_desc,
        NatTrans.inr_leibnizBox_assoc, h]
  Arrow.isoMk hp.isoPushout.symm (φG.app X) hw

end Monoidal

end CategoryTheory
