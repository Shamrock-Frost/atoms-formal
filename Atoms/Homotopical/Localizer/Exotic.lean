import Atoms.Homotopical.Localizer.BaseChange
import Atoms.Homotopical.Localizer.LeftProper

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace Atoms.Homotopical

universe v

variable {A : Type v} [SmallCategory A]

theorem llp_rlp_le_monomorphisms (I : MorphismProperty (Aᵒᵖ ⥤ Type v))
    (hI : I ≤ monomorphisms _) : I.rlp.llp ≤ monomorphisms (Aᵒᵖ ⥤ Type v) := by
  refine (antitone_llp (antitone_rlp hI)).trans (le_of_eq ?_)
  rw [← llp_rlp_cellularGenerators, rlp_llp_rlp]

section Bounds

variable (W : MorphismProperty (Aᵒᵖ ⥤ Type v)) [IsAccessibleALocalizer W]
  (I : MorphismProperty (Aᵒᵖ ⥤ Type v)) [I.IsSmall.{v}]

private theorem exists_bound :
    ∃ β : Cardinal.{v}, (∀ ⦃X Y : Aᵒᵖ ⥤ Type v⦄ (i : X ⟶ Y), I i → IsBounded β Y) ∧
      ∀ {X Y : Aᵒᵖ ⥤ Type v} (w : X ⟶ Y), (monomorphisms _ ⊓ W) w →
        ∀ K : Subfunctor Y, IsBounded β K.toFunctor →
          ∃ L : Subfunctor Y, K ≤ L ∧ IsBounded β L.toFunctor ∧
            (monomorphisms _ ⊓ W)
              (Subfunctor.homOfLe (inf_le_right : Subfunctor.range w ⊓ L ≤ L)) := by
  obtain ⟨S, hS, hmono, hWeq⟩ := IsAccessibleALocalizer.exists_lawvereCylinder (V := W)
  have : S.IsSmall.{v} := hS
  obtain ⟨α₀, -, henl⟩ := (lawvereCylinder A).exists_bounded_enlargement S hmono
  rw [ExactCylinder.trivialCofibrations, hWeq] at henl
  obtain ⟨κ, U, V, f, hf⟩ := (isSmall_iff_eq_ofHoms.{v} I).1 inferInstance
  obtain ⟨c, hc⟩ := exists_isBounded_forall V
  refine ⟨2 ^ max α₀ c, fun X Y i hi ↦ ?_, henl _ (le_max_left _ _)⟩
  rw [hf] at hi
  obtain ⟨t⟩ := hi
  exact (hc t).mono ((le_max_right _ _).trans (Cardinal.cantor _).le)

end Bounds

section Lifting

variable {W I : MorphismProperty (Aᵒᵖ ⥤ Type v)}

private structure ExoticBound (W I P : MorphismProperty (Aᵒᵖ ⥤ Type v)) (β : Cardinal.{v}) :
    Prop where
  isBounded ⦃X Y : Aᵒᵖ ⥤ Type v⦄ (i : X ⟶ Y) : I i → IsBounded β Y
  enlarge {X Y : Aᵒᵖ ⥤ Type v} (w : X ⟶ Y) : (monomorphisms _ ⊓ W) w →
    ∀ K : Subfunctor Y, IsBounded β K.toFunctor →
      ∃ L : Subfunctor Y, K ≤ L ∧ IsBounded β L.toFunctor ∧
        (monomorphisms _ ⊓ W) (Subfunctor.homOfLe (inf_le_right : Subfunctor.range w ⊓ L ≤ L))
  factor {X Y : Aᵒᵖ ⥤ Type v} (f : X ⟶ Y) : IsBounded β Y → (monomorphisms _ ⊓ W) f →
    ∃ (M : Aᵒᵖ ⥤ Type v) (j : X ⟶ M) (q : M ⟶ Y), P.llp j ∧ I.rlp q ∧ j ≫ q = f

variable {P : MorphismProperty (Aᵒᵖ ⥤ Type v)} {β : Cardinal.{v}}

private theorem ExoticBound.exists_comp_eq_of_mono (h : ExoticBound W I P β)
    {A' B X Y : Aᵒᵖ ⥤ Type v} {i : A' ⟶ B} (hi : I i) {w : X ⟶ Y}
    (hw : (monomorphisms _ ⊓ W) w) (sq : Arrow.mk i ⟶ Arrow.mk w) :
    ∃ (j : Arrow (Aᵒᵖ ⥤ Type v)) (_ : P.llp j.hom) (φ : Arrow.mk i ⟶ j) (ψ : j ⟶ Arrow.mk w),
      φ ≫ ψ = sq := by
  have : Mono w := hw.1
  obtain ⟨L, hKL, hLb, hLW⟩ := h.enlarge w hw _ (isBounded_range sq.right (h.isBounded i hi))
  let N := Subfunctor.range w ⊓ L
  obtain ⟨M, j, q, hj, hq, hjq⟩ := h.factor (Subfunctor.homOfLe (inf_le_right : N ≤ L)) hLb hLW
  obtain ⟨a₀, ha₀⟩ := Subfunctor.exists_comp_eq_of_range_le w N.ι
    (by rw [Subfunctor.range_ι]; exact inf_le_left)
  have hsq : sq.left ≫ w = i ≫ sq.right := Arrow.w sq
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : A' ⟶ N.toFunctor, u₀ ≫ N.ι = sq.left ≫ w :=
    ⟨Subfunctor.lift _ (le_inf (Subfunctor.range_comp_le _ _)
      (by rw [hsq]; exact (Subfunctor.range_comp_le _ _).trans hKL)), Subfunctor.lift_ι _ _⟩
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : B ⟶ L.toFunctor, b₀ ≫ L.ι = sq.right :=
    ⟨Subfunctor.lift _ hKL, Subfunctor.lift_ι _ _⟩
  have sq₂ : CommSq (u₀ ≫ j) i q b₀ := ⟨by
    rw [← cancel_mono L.ι, Category.assoc, Category.assoc, reassoc_of% hjq,
      Subfunctor.homOfLe_ι, hu₀, Category.assoc, hb₀, hsq]⟩
  have := hq i hi
  refine ⟨Arrow.mk j, hj, Arrow.homMk u₀ sq₂.lift sq₂.fac_left.symm,
    Arrow.homMk a₀ (q ≫ L.ι) ?_, Arrow.hom_ext _ _ ?_ ?_⟩
  · simp only [Arrow.mk_hom]
    rw [ha₀, reassoc_of% hjq, Subfunctor.homOfLe_ι]
  · simp only [Arrow.comp_left, Arrow.homMk_left, Arrow.mk_left]
    rw [← cancel_mono w, Category.assoc, ha₀, hu₀]
  · simp only [Arrow.comp_right, Arrow.homMk_right, Arrow.mk_right]
    rw [reassoc_of% sq₂.fac_right, hb₀]

private theorem ExoticBound.exists_comp_eq [hW : IsALocalizer W] (h : ExoticBound W I P β)
    (hI : I ≤ monomorphisms _) {A' B X Y : Aᵒᵖ ⥤ Type v} {i : A' ⟶ B} (hi : I i) {p : X ⟶ Y}
    (hp : W p) (sq : Arrow.mk i ⟶ Arrow.mk p) :
    ∃ (j : Arrow (Aᵒᵖ ⥤ Type v)) (_ : P.llp j.hom) (φ : Arrow.mk i ⟶ j) (ψ : j ⟶ Arrow.mk p),
      φ ≫ ψ = sq := by
  let d := factorizationData (monomorphisms (Aᵒᵖ ⥤ Type v)) (monomorphisms _).rlp p
  have hdi : (monomorphisms _ ⊓ W) d.i :=
    ⟨d.hi, W.of_postcomp _ _ (hW.rlp_monomorphisms_le _ d.hp) (by rw [d.fac]; exact hp)⟩
  have sq₁ : CommSq (sq.left ≫ d.i) i d.p sq.right :=
    ⟨by rw [Category.assoc, d.fac]; exact Arrow.w sq⟩
  have := d.hp i (hI i hi)
  obtain ⟨j, hj, φ, ψ, hφψ⟩ :=
    h.exists_comp_eq_of_mono hi hdi (Arrow.homMk sq.left sq₁.lift sq₁.fac_left.symm)
  refine ⟨j, hj, φ, ψ ≫ Arrow.homMk (𝟙 X) d.p (by simp), ?_⟩
  rw [← Category.assoc, hφψ]
  refine Arrow.hom_ext _ _ ?_ ?_
  · simp only [Arrow.comp_left, Arrow.homMk_left]
    exact Category.comp_id _
  · simp only [Arrow.comp_right, Arrow.homMk_right]
    exact sq₁.fac_right

private theorem ExoticBound.inf_le_rlp [IsALocalizer W] (h : ExoticBound W I P β)
    (hI : I ≤ monomorphisms _) : P ⊓ W ≤ I.rlp := by
  intro X Y p hp A' B i hi
  refine ⟨fun {a b} sq ↦ ?_⟩
  obtain ⟨j, hj, φ, ψ, hφψ⟩ := h.exists_comp_eq hI hi hp.2 (Arrow.homMk a b sq.w)
  have := hj p hp.1
  have sq' : CommSq ψ.left j.hom p ψ.right := ⟨Arrow.w ψ⟩
  have hφ : i ≫ φ.right = φ.left ≫ j.hom := (Arrow.w φ).symm
  refine ⟨⟨{ l := φ.right ≫ sq'.lift, fac_left := ?_, fac_right := ?_ }⟩⟩
  · rw [reassoc_of% hφ, sq'.fac_left, ← Arrow.comp_left, hφψ]
    rfl
  · rw [Category.assoc, sq'.fac_right, ← Arrow.comp_right, hφψ]
    rfl

end Lifting

section Generators

variable (W : MorphismProperty (Aᵒᵖ ⥤ Type v)) [IsAccessibleALocalizer W]
  (I : MorphismProperty (Aᵒᵖ ⥤ Type v))

private theorem llp_rlp_eq_of_rlp_inf_eq (hI : I ≤ monomorphisms _)
    {J : MorphismProperty (Aᵒᵖ ⥤ Type v)} [J.IsSmall.{v}] (hJ : J ≤ I.rlp.llp ⊓ W)
    (hJI : J.rlp ⊓ W = I.rlp) : J.rlp.llp = I.rlp.llp ⊓ W := by
  have := IsAccessibleALocalizer.isWeakFactorizationSystem_trivialCofibrations (V := W)
  have hle : J.rlp.llp ≤ I.rlp.llp ⊓ W := by
    refine le_inf (antitone_llp (hJI.symm.le.trans inf_le_left)) ?_
    have h := antitone_llp
      (antitone_rlp (hJ.trans (inf_le_inf_right W (llp_rlp_le_monomorphisms I hI))))
    rw [llp_eq_of_wfs (monomorphisms _ ⊓ W) (monomorphisms _ ⊓ W).rlp] at h
    exact h.trans inf_le_right
  refine le_antisymm hle fun X Y g hg ↦ ?_
  let d := factorizationData J.rlp.llp J.rlp g
  have hq : I.rlp d.p := by
    rw [← hJI]
    exact ⟨d.hp, W.of_precomp _ _ (hle _ d.hi).2 (by rw [d.fac]; exact hg.2)⟩
  have := hg.1 _ hq
  exact J.rlp.llp.of_retract (RetractArrow.ofLeftLiftingProperty d.fac) d.hi

variable [I.IsSmall.{v}]

theorem exists_exoticGenerators (hI : I ≤ monomorphisms _) (hIW : I.rlp ≤ W) :
    ∃ J : MorphismProperty (Aᵒᵖ ⥤ Type v), J.IsSmall.{v} ∧ J ≤ I.rlp.llp ⊓ W ∧
      J.rlp ⊓ W = I.rlp ∧ J.rlp.llp = I.rlp.llp ⊓ W := by
  obtain ⟨β, hB, henl⟩ := exists_bound W I
  obtain ⟨ι, R, -, hrep⟩ := exists_boundedRepresentatives (A := A) β
  let F := fun t : Σ k : ι × ι, {f : R k.1 ⟶ R k.2 // (monomorphisms _ ⊓ W) f} ↦
    factorizationData I.rlp.llp I.rlp t.2.1
  let J := MorphismProperty.ofHoms fun t ↦ (F t).i
  have hJ : J ≤ I.rlp.llp ⊓ W := by
    rintro _ _ _ ⟨t⟩
    exact ⟨(F t).hi, W.of_postcomp _ _ (hIW _ (F t).hp) (by rw [(F t).fac]; exact t.2.2.2)⟩
  have hP : ExoticBound W I J.rlp β := by
    refine ⟨hB, henl, fun {X Y} f hY hf ↦ ?_⟩
    have : Mono f := hf.1
    obtain ⟨k₁, ⟨e₁⟩⟩ := hrep X (hY.of_mono f)
    obtain ⟨k₂, ⟨e₂⟩⟩ := hrep Y hY
    let t : Σ k : ι × ι, {f : R k.1 ⟶ R k.2 // (monomorphisms _ ⊓ W) f} :=
      ⟨(k₁, k₂), e₁.inv ≫ f ≫ e₂.hom,
        RespectsIso.precomp _ _ _ (RespectsIso.postcomp _ _ _ hf)⟩
    refine ⟨(F t).Z, e₁.hom ≫ (F t).i, (F t).p ≫ e₂.inv,
      J.rlp.llp.comp_mem _ _ (llp_of_isIso _ _) (le_llp_rlp J _ ⟨t⟩),
      I.rlp.comp_mem _ _ (F t).hp (rlp_of_isIso _ _), ?_⟩
    rw [Category.assoc, (F t).fac_assoc]
    simp only [t, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have hJI : J.rlp ⊓ W = I.rlp := le_antisymm (hP.inf_le_rlp hI)
    (le_inf ((rlp_llp_rlp I).symm.le.trans (antitone_rlp (hJ.trans inf_le_left))) hIW)
  exact ⟨J, inferInstance, hJ, hJI, llp_rlp_eq_of_rlp_inf_eq W I hI hJ hJI⟩

end Generators

section ModelStructure

variable (W : MorphismProperty (Aᵒᵖ ⥤ Type v)) [IsAccessibleALocalizer W]
  (I : MorphismProperty (Aᵒᵖ ⥤ Type v)) [I.IsSmall.{v}]

private theorem rlp_inf_inf_eq (hI : I ≤ monomorphisms _) (hIW : I.rlp ≤ W) :
    (I.rlp.llp ⊓ W).rlp ⊓ W = I.rlp := by
  obtain ⟨J, -, -, hJI, hJ⟩ := exists_exoticGenerators W I hI hIW
  rw [← hJ, rlp_llp_rlp, hJI]

private theorem isWeakFactorizationSystem_llp_rlp (hI : I ≤ monomorphisms _) (hIW : I.rlp ≤ W) :
    IsWeakFactorizationSystem I.rlp.llp ((I.rlp.llp ⊓ W).rlp ⊓ W) := by
  rw [rlp_inf_inf_eq W I hI hIW]
  exact ⟨rlp_llp_rlp I, rfl, inferInstance⟩

private theorem isWeakFactorizationSystem_llp_rlp_inf (hI : I ≤ monomorphisms _)
    (hIW : I.rlp ≤ W) : IsWeakFactorizationSystem (I.rlp.llp ⊓ W) (I.rlp.llp ⊓ W).rlp := by
  obtain ⟨J, hJs, -, -, hJ⟩ := exists_exoticGenerators W I hI hIW
  rw [← hJ, rlp_llp_rlp]
  exact ⟨rlp_llp_rlp J, rfl, inferInstance⟩

@[instance_reducible]
def exoticModelCategory (hI : I ≤ monomorphisms _) (hIW : I.rlp ≤ W) :
    ModelCategory (Aᵒᵖ ⥤ Type v) :=
  letI : CategoryWithCofibrations (Aᵒᵖ ⥤ Type v) := ⟨I.rlp.llp⟩
  letI : CategoryWithWeakEquivalences (Aᵒᵖ ⥤ Type v) := ⟨W⟩
  letI : CategoryWithFibrations (Aᵒᵖ ⥤ Type v) := ⟨(I.rlp.llp ⊓ W).rlp⟩
  haveI : (weakEquivalences (Aᵒᵖ ⥤ Type v)).HasTwoOutOfThreeProperty :=
    inferInstanceAs W.HasTwoOutOfThreeProperty
  haveI : IsWeakFactorizationSystem (cofibrations (Aᵒᵖ ⥤ Type v))
      (trivialFibrations (Aᵒᵖ ⥤ Type v)) := isWeakFactorizationSystem_llp_rlp W I hI hIW
  haveI : IsWeakFactorizationSystem (trivialCofibrations (Aᵒᵖ ⥤ Type v))
      (fibrations (Aᵒᵖ ⥤ Type v)) := isWeakFactorizationSystem_llp_rlp_inf W I hI hIW
  ModelCategory.mk' _

namespace exoticModelCategory

variable {W I} (hI : I ≤ monomorphisms _) (hIW : I.rlp ≤ W)

theorem cofibrations_eq :
    letI := exoticModelCategory W I hI hIW
    cofibrations (Aᵒᵖ ⥤ Type v) = I.rlp.llp := rfl

theorem weakEquivalences_eq :
    letI := exoticModelCategory W I hI hIW
    weakEquivalences (Aᵒᵖ ⥤ Type v) = W := rfl

theorem fibrations_eq :
    letI := exoticModelCategory W I hI hIW
    fibrations (Aᵒᵖ ⥤ Type v) = (I.rlp.llp ⊓ W).rlp := rfl

theorem trivialFibrations_eq :
    letI := exoticModelCategory W I hI hIW
    trivialFibrations (Aᵒᵖ ⥤ Type v) = I.rlp :=
  rlp_inf_inf_eq W I hI hIW

theorem exists_fibrations_eq_rlp :
    letI := exoticModelCategory W I hI hIW
    ∃ J : MorphismProperty (Aᵒᵖ ⥤ Type v), J.IsSmall.{v} ∧
      trivialCofibrations (Aᵒᵖ ⥤ Type v) = J.rlp.llp ∧ fibrations (Aᵒᵖ ⥤ Type v) = J.rlp := by
  obtain ⟨J, hJs, -, -, hJ⟩ := exists_exoticGenerators W I hI hIW
  refine ⟨J, hJs, hJ.symm, ?_⟩
  rw [fibrations_eq, ← hJ, rlp_llp_rlp]

end exoticModelCategory

end ModelStructure

namespace exoticModelCategory

variable {W I : MorphismProperty (Aᵒᵖ ⥤ Type v)}

theorem mem_of_isPushout [IsAccessibleALocalizer W] (hI : I ≤ monomorphisms _)
    {E D B P : Aᵒᵖ ⥤ Type v} {j : E ⟶ D} {w : E ⟶ B} {q : D ⟶ P} {j' : B ⟶ P}
    (h : IsPushout j w q j') (hj : I.rlp.llp j) (hw : W w) : W q :=
  have : Mono j := llp_rlp_le_monomorphisms I hI j hj
  IsALocalizer.mem_of_isPushout h hw

theorem rlp_le_fibrations (hI : I ≤ monomorphisms _) :
    (monomorphisms (Aᵒᵖ ⥤ Type v) ⊓ W).rlp ≤ (I.rlp.llp ⊓ W).rlp :=
  antitone_rlp (inf_le_inf_right W (llp_rlp_le_monomorphisms I hI))

theorem isRightProper_of_weakFibration (hI : I ≤ monomorphisms _)
    (h : ∀ {E B : Aᵒᵖ ⥤ Type v} (p : E ⟶ B), (I.rlp.llp ⊓ W).rlp p → WeakFibration W p) :
    IsRightProper W :=
  ⟨fun p hp ↦ h p (rlp_le_fibrations hI p hp)⟩

end exoticModelCategory

end Atoms.Homotopical
