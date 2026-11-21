import Atoms.Shape.MarkedHornGrayTensor

open CategoryTheory Order Set Atoms.Molecule Atoms.Molecule.OGP

universe u

namespace Atoms.Molecule.OGP

namespace IsStagedPasting

variable {P : OGP.{u}} {m : ℕ} {X : LowerSet P} {L R M : ℕ → LowerSet P}

theorem dual_cond (J : ℕ → Bool) (h : P.IsStagedPasting m X L R M) :
    (OGP.dual P J).IsStagedPasting m X (fun i => cond (J i) (R i) (L i))
      (fun i => cond (J i) (L i) (R i)) M := by
  refine ⟨h.stage_zero, fun i hi => (isMoleculeIn_dual J).2 (h.isMoleculeIn_stage i hi),
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · have h1 := (h.stage_succ i hi).1
    have h2 := (h.stage_succ i hi).2
    cases hj : J (i + 1)
    · exact ⟨(isPastingIn_dual J).2 (by rw [hj]; exact h1),
        (isPastingIn_dual J).2 (by rw [hj]; exact h2)⟩
    · have h1' : (OGP.dual P J).IsPastingIn i (M i) (L (i + 1)) (L (i + 1) ⊔ M i) :=
        (isPastingIn_dual J).2 (by rw [hj]; exact h1)
      have h2' : (OGP.dual P J).IsPastingIn i (R (i + 1)) (L (i + 1) ⊔ M i) (M (i + 1)) :=
        (isPastingIn_dual J).2 (by rw [hj]; exact h2)
      exact ⟨h1'.isPastingIn_left_sup h2', h1'.assoc_symm h2'⟩
  · cases J (i + 1)
    · exact ⟨(isMoleculeIn_dual J).2 (h.isMoleculeIn_left i hi).1, (h.isMoleculeIn_left i hi).2⟩
    · exact ⟨(isMoleculeIn_dual J).2 (h.isMoleculeIn_right i hi).1,
        (h.isMoleculeIn_right i hi).2⟩
  · cases J (i + 1)
    · exact ⟨(isMoleculeIn_dual J).2 (h.isMoleculeIn_right i hi).1,
        (h.isMoleculeIn_right i hi).2⟩
    · exact ⟨(isMoleculeIn_dual J).2 (h.isMoleculeIn_left i hi).1, (h.isMoleculeIn_left i hi).2⟩

theorem ofDual_cond (J : ℕ → Bool) (h : (OGP.dual P J).IsStagedPasting m X L R M) :
    P.IsStagedPasting m X (fun i => cond (J i) (R i) (L i)) (fun i => cond (J i) (L i) (R i)) M :=
  (congrArg (fun o => IsStagedPasting { P with orient := o } m X
    (fun i => cond (J i) (R i) (L i)) (fun i => cond (J i) (L i) (R i)) M)
    (orient_dual_dual P J)).mp (h.dual_cond J)

end IsStagedPasting

end Atoms.Molecule.OGP

namespace Atoms.Molecule.OGP

variable {P Q : OGP.{u}}

theorem stagedTops_cond {m : ℕ} {L R : ℕ → LowerSet P} {T : P → Prop} (J : ℕ → Bool) :
    StagedTops m (fun i => cond (J i) (R i) (L i)) (fun i => cond (J i) (L i) (R i)) T ↔
      StagedTops m L R T := by
  refine forall₂_congr fun i _ => forall_congr' fun y => imp_congr_left ?_
  change y ∈ cond (J (i + 1)) (R (i + 1)) (L (i + 1)) ⊔ cond (J (i + 1)) (L (i + 1)) (R (i + 1)) ↔
    y ∈ L (i + 1) ⊔ R (i + 1)
  cases J (i + 1)
  · rfl
  · exact or_comm

private theorem xor_bodd_add_succ (k d : ℕ) (α : Bool) :
    xor (k + d + 1).bodd (xor (k + 1).bodd α) = xor d.bodd α := by
  rw [show k + d + 1 = k + 1 + d by omega, Nat.bodd_add]
  cases (k + 1).bodd <;> cases d.bodd <;> cases α <;> rfl

theorem exists_isStagedPasting_grayProduct_right {U : LowerSet P} {X V : LowerSet Q} {k d : ℕ}
    {L R M : ℕ → LowerSet Q} (hU : IsMoleculeIn P U) (hV : IsMoleculeIn Q V)
    (hdU : krullDim U ≤ d) (hdV : krullDim V ≤ (k + 1 : ℕ)) {α : Bool}
    (hs : Q.IsStagedPasting k X L R M) (hM : M k = Q.boundary V k α) {T : Q → Prop}
    (ht : StagedTops k L R T) :
    ∃ L' R' M' : ℕ → LowerSet (grayProduct P Q),
      (grayProduct P Q).IsStagedPasting (k + d) (U ×ˢ X) L' R' M' ∧
      M' (k + d) = (grayProduct P Q).boundary (U ×ˢ V) (k + d) (xor d.bodd α) ∧
      StagedTops (k + d) L' R' (fun z => T z.2 ∨ (z.2 ∈ V ∧ grade ℕ z.2 = k + 1 ∧
        ∃ ℓ < d, ∃ σ, z.1 ∈ P.boundary U ℓ σ)) := by
  have hM' : M k = (OGP.dual Q Nat.bodd).boundary V k (xor (k + 1).bodd α) := by
    rw [hM, boundary_dual, Bool.xor_xor_cancel_left]
  obtain ⟨L₁, R₁, M₁, hs₁, hM₁, ht₁⟩ := exists_isStagedPasting_grayProduct_left
    (P := OGP.dual Q Nat.bodd) (Q := OGP.dual P Nat.bodd) ((isMoleculeIn_dual Nat.bodd).2 hV)
    ((isMoleculeIn_dual Nat.bodd).2 hU) hdV hdU (hs.dual_cond Nat.bodd) hM'
    ((stagedTops_cond Nat.bodd).2 ht)
  have hs₂ := (hs₁.map (grayProductSwap P Q).inv).ofDual_cond Nat.bodd
  rw [map_grayProductSwap_inv_prod] at hs₂
  refine ⟨_, _, _, hs₂, ?_, (stagedTops_cond Nat.bodd).2 fun i hi y hy hyd => ?_⟩
  · dsimp only
    rw [hM₁, map_grayProductSwap_inv_boundary_prod, xor_bodd_add_succ]
  · rw [← OGP.map_sup] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hgz : grade ℕ z = i + 1 :=
      ((isMorphism (grayProductSwap P Q).inv).grade_eq z).symm.trans hyd
    rcases ht₁ i hi z hz hgz with h1 | ⟨h1, h2, ℓ, hℓ, h3⟩
    · exact Or.inl h1
    · rw [boundary_dual] at h3
      exact Or.inr ⟨h1, h2, ℓ, hℓ, _, h3⟩

end Atoms.Molecule.OGP

namespace Atoms.Shape

namespace MarkedHornData

variable (V : Atom) (h : MarkedHornData)

def grayTensorLeftFace : (Atom.grayTensor V h.atom).ogp :=
  (Atom.grayTensorIso V h.atom).hom (V.top, h.face)

def grayTensorLeftMarking (marked : Bool) : Set (Atom.grayTensor V h.atom).ogp :=
  {w | ((Atom.grayTensorIso V h.atom).inv w).2 ∈ h.marking ∨
    (((Atom.grayTensorIso V h.atom).inv w).2 ∈ h.targetMarking ∧
      ((Atom.grayTensorIso V h.atom).inv w).1 ∈ V.ogp.bdryFull ⊤) ∨
    (marked = true ∧ ((Atom.grayTensorIso V h.atom).inv w).2 ∈ h.hornSet ∧
      ((Atom.grayTensorIso V h.atom).inv w).1 = V.top)}

theorem Iic_grayTensorLeftFace :
    LowerSet.Iic (h.grayTensorLeftFace V) =
      map (Atom.grayTensorIso V h.atom).hom ((⊤ : LowerSet V.ogp) ×ˢ LowerSet.Iic h.face) := by
  rw [grayTensorLeftFace, ← map_Iic, Iic_grayProduct, V.Iic_top]

theorem dimension_grayTensorLeft_sub_one :
    (Atom.grayTensor V h.atom).dimension - 1 = h.atom.dimension - 1 + V.dimension := by
  have := h.positive
  rw [Atom.dimension_grayTensor]
  omega

theorem exists_isStagedPasting_grayTensorLeft :
    ∃ L R M : ℕ → LowerSet (Atom.grayTensor V h.atom).ogp,
      (Atom.grayTensor V h.atom).ogp.IsStagedPasting ((Atom.grayTensor V h.atom).dimension - 1)
        (.Iic (h.grayTensorLeftFace V)) L R M ∧
      M ((Atom.grayTensor V h.atom).dimension - 1) =
        (Atom.grayTensor V h.atom).ogp.bdry ⊤ (xor V.dimension.bodd h.side) ∧
      ∀ i < (Atom.grayTensor V h.atom).dimension - 1, ∀ y ∈ L (i + 1) ⊔ R (i + 1),
        grade ℕ y = i + 1 → y ∈ h.grayTensorLeftMarking V false := by
  have hpos := h.positive
  set e := Atom.grayTensorIso V h.atom with he
  have hU := h.atom.toMoleculeShape.krullDim_top_eq (n := h.atom.dimension - 1)
    (Nat.sub_add_cancel hpos).symm
  have hdV : krullDim (⊤ : LowerSet V.ogp) ≤ (V.dimension : ℕ) := by
    rw [LowerSet.krullDim_top, V.krullDim_eq_dimension]
  have hM : h.stage (h.atom.dimension - 1) =
      h.atom.ogp.boundary ⊤ (h.atom.dimension - 1) h.side := by
    rw [h.stage_last, h.atom.bdry_top_eq_boundary hpos]
  obtain ⟨L, R, M, hs, hM', ht⟩ := OGP.exists_isStagedPasting_grayProduct_right (P := V.ogp)
    V.isMolecule h.atom.isMolecule hdV hU.le h.staged hM h.marked_tops
  have hW : 0 < (Atom.grayTensor V h.atom).dimension :=
    (HornData.grayTensorLeft V h.toHornData).positive
  refine ⟨fun i => map e.hom (L i), fun i => map e.hom (R i), fun i => map e.hom (M i), ?_, ?_,
    fun i hi y hy hyd => ?_⟩
  · rw [dimension_grayTensorLeft_sub_one, Iic_grayTensorLeftFace]
    exact hs.map e.hom
  · dsimp only
    rw [dimension_grayTensorLeft_sub_one, hM', (Atom.grayTensor V h.atom).bdry_top_eq_boundary hW,
      dimension_grayTensorLeft_sub_one, map_boundary, LowerSet.top_prod_top, map_top_of_isIso]
  · rw [← OGP.map_sup] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hgz : grade ℕ z = i + 1 := ((isMorphism e.hom).grade_eq z).symm.trans hyd
    rw [dimension_grayTensorLeft_sub_one] at hi
    rw [grayTensorLeftMarking, Set.mem_ofPred_eq, he, Iso.hom_inv_id_apply]
    rcases ht i hi z hz hgz with hm | ⟨-, hzd, ℓ, hℓ, σ, hz1⟩
    · exact Or.inl hm
    · refine Or.inr (Or.inl ⟨h.mem_targetMarking_iff.2 (Or.inl (GradeOrder.eq_of_le_of_grade_le
        (h.atom.le_top _) (by rw [← h.atom.dimension_eq]; omega))), ?_⟩)
      refine (V.mem_bdryFull_top_iff _).2 fun h2 => ?_
      have := grade_le_of_mem_boundary hz1
      rw [h2, ← V.dimension_eq] at this
      omega

theorem grayTensorLeftFace_mem_faces :
    h.grayTensorLeftFace V ∈ (Atom.grayTensor V h.atom).ogp.faces (xor V.dimension.bodd h.side)
      (Atom.grayTensor V h.atom).top := by
  obtain ⟨L, R, M, hs, hM, -⟩ := h.exists_isStagedPasting_grayTensorLeft V
  have hx := hs.stage_le 0 _ (Nat.zero_le _) le_rfl
    (hs.stage_zero ▸ LowerSet.mem_Iic_iff.2 le_rfl)
  rw [hM, ← (Atom.grayTensor V h.atom).Iic_top] at hx
  refine mem_faces_of_mem_bdry_Iic hx ?_
  have h1 : grade ℕ (h.grayTensorLeftFace V) = grade ℕ V.top + grade ℕ h.face :=
    (isMorphism (Atom.grayTensorIso V h.atom).hom).grade_eq _
  rw [h1, ← (Atom.grayTensor V h.atom).dimension_eq, Atom.dimension_grayTensor,
    ← V.dimension_eq, ← h.dim_face_add_one]
  omega

theorem mem_hornSet_grayTensorLeftFace {w : (Atom.grayTensor V h.atom).ogp}
    (hw : ((Atom.grayTensorIso V h.atom).inv w).1 ∈ V.ogp.bdryFull ⊤ ∨
      ((Atom.grayTensorIso V h.atom).inv w).2 ∈ h.hornSet) :
    w ∈ ((Atom.grayTensor V h.atom).isRewritableSubmolecule_Iic_of_mem_faces
        (h.grayTensorLeftFace_mem_faces V)).hornSet (Atom.grayTensor V h.atom).isMolecule
        (Atom.grayTensor V h.atom).isAtom.isRound := by
  have hne : (Atom.grayTensorIso V h.atom).inv w ≠ (V.top, h.atom.top) ∧
      (Atom.grayTensorIso V h.atom).inv w ≠ (V.top, h.face) := by
    rcases hw with hw | hw
    · exact ⟨fun e => (V.mem_bdryFull_top_iff _).1 hw (congrArg Prod.fst e),
        fun e => (V.mem_bdryFull_top_iff _).1 hw (congrArg Prod.fst e)⟩
    · obtain ⟨hb, hf⟩ := h.mem_hornSet_iff.1 hw
      exact ⟨fun e => (h.atom.mem_bdryFull_top_iff _).1 hb (congrArg Prod.snd e),
        fun e => hf (congrArg Prod.snd e)⟩
  refine (mem_hornSet_closure_singleton_iff ⟨Atom.grayTensor V h.atom,
    (HornData.grayTensorLeft V h.toHornData).positive, xor V.dimension.bodd h.side,
    .Iic (h.grayTensorLeftFace V),
    (Atom.grayTensor V h.atom).isRewritableSubmolecule_Iic_of_mem_faces
      (h.grayTensorLeftFace_mem_faces V)⟩ rfl).2 ⟨fun e => hne.1 ?_, fun e => hne.2 ?_⟩
  · rw [e, Atom.grayTensorIso_inv_top]
  · rw [e, grayTensorLeftFace, Iso.hom_inv_id_apply]

theorem grayTensorLeftMarking_false_subset (marked : Bool) :
    h.grayTensorLeftMarking V false ⊆ h.grayTensorLeftMarking V marked := by
  rintro w (hw | hw | ⟨hw, -⟩)
  · exact Or.inl hw
  · exact Or.inr (Or.inl hw)
  · exact absurd hw Bool.false_ne_true

theorem grayTensorLeftMarking_mem {marked : Bool} (hV : marked = true → 0 < V.dimension) :
    ∀ w ∈ h.grayTensorLeftMarking V marked,
      w ∈ ((Atom.grayTensor V h.atom).isRewritableSubmolecule_Iic_of_mem_faces
          (h.grayTensorLeftFace_mem_faces V)).hornSet (Atom.grayTensor V h.atom).isMolecule
          (Atom.grayTensor V h.atom).isAtom.isRound ∧ 0 < grade ℕ w := by
  intro w hw
  have hg : grade ℕ w = grade ℕ ((Atom.grayTensorIso V h.atom).inv w).1 +
      grade ℕ ((Atom.grayTensorIso V h.atom).inv w).2 :=
    ((isMorphism (Atom.grayTensorIso V h.atom).inv).grade_eq w).symm
  rcases hw with hw | ⟨hw, hw'⟩ | ⟨hm, hw, hw'⟩
  · exact ⟨h.mem_hornSet_grayTensorLeftFace V (Or.inr (h.marking_mem _ hw).1),
      by have := (h.marking_mem _ hw).2; omega⟩
  · exact ⟨h.mem_hornSet_grayTensorLeftFace V (Or.inl hw'),
      by have := (h.targetMarking_mem _ hw).2; omega⟩
  · refine ⟨h.mem_hornSet_grayTensorLeftFace V (Or.inr hw), ?_⟩
    have := hV hm
    rw [hw', ← V.dimension_eq] at hg
    omega

def grayTensorLeft (marked : Bool) (hV : marked = true → 0 < V.dimension)
    (L R M : ℕ → LowerSet (Atom.grayTensor V h.atom).ogp)
    (staged : (Atom.grayTensor V h.atom).ogp.IsStagedPasting
      ((Atom.grayTensor V h.atom).dimension - 1) (.Iic (h.grayTensorLeftFace V)) L R M)
    (stage_last : M ((Atom.grayTensor V h.atom).dimension - 1) =
      (Atom.grayTensor V h.atom).ogp.bdry ⊤ (xor V.dimension.bodd h.side))
    (tops : ∀ i < (Atom.grayTensor V h.atom).dimension - 1, ∀ y ∈ L (i + 1) ⊔ R (i + 1),
      grade ℕ y = i + 1 → y ∈ h.grayTensorLeftMarking V false) : MarkedHornData where
  atom := Atom.grayTensor V h.atom
  positive := (HornData.grayTensorLeft V h.toHornData).positive
  side := xor V.dimension.bodd h.side
  face := h.grayTensorLeftFace V
  face_mem := h.grayTensorLeftFace_mem_faces V
  marking := h.grayTensorLeftMarking V marked
  marking_mem := h.grayTensorLeftMarking_mem V hV
  left := L
  right := R
  stage := M
  staged := staged
  stage_last := stage_last
  marked_tops i hi y hy hyd := h.grayTensorLeftMarking_false_subset V marked (tops i hi y hy hyd)

section GrayTensorLeft

variable {marked : Bool} {hV : marked = true → 0 < V.dimension}
  {L R M : ℕ → LowerSet (Atom.grayTensor V h.atom).ogp}
  {hs : (Atom.grayTensor V h.atom).ogp.IsStagedPasting
    ((Atom.grayTensor V h.atom).dimension - 1) (.Iic (h.grayTensorLeftFace V)) L R M}
  {hM : M ((Atom.grayTensor V h.atom).dimension - 1) =
    (Atom.grayTensor V h.atom).ogp.bdry ⊤ (xor V.dimension.bodd h.side)}
  {ht : ∀ i < (Atom.grayTensor V h.atom).dimension - 1, ∀ y ∈ L (i + 1) ⊔ R (i + 1),
    grade ℕ y = i + 1 → y ∈ h.grayTensorLeftMarking V false}

theorem toHornData_grayTensorLeft :
    (h.grayTensorLeft V marked hV L R M hs hM ht).toHornData =
      HornData.grayTensorLeft V h.toHornData :=
  HornData.eq_of_removed_eq (HornData.grayTensorLeft V h.toHornData) _ _
    (h.Iic_grayTensorLeftFace V).symm

theorem mem_hornSet_grayTensorLeft_iff {w : (Atom.grayTensor V h.atom).ogp} :
    w ∈ (h.grayTensorLeft V marked hV L R M hs hM ht).hornSet ↔
      ((Atom.grayTensorIso V h.atom).inv w).1 ∈ V.ogp.bdryFull ⊤ ∨
        ((Atom.grayTensorIso V h.atom).inv w).2 ∈ h.hornSet := by
  refine ((h.grayTensorLeft V marked hV L R M hs hM ht).mem_hornSet_iff).trans ?_
  change w ∈ (Atom.grayTensor V h.atom).ogp.bdryFull ⊤ ∧ w ≠ h.grayTensorLeftFace V ↔ _
  have hw : w = (Atom.grayTensorIso V h.atom).hom ((Atom.grayTensorIso V h.atom).inv w) :=
    (Iso.inv_hom_id_apply _ w).symm
  have htop : (Atom.grayTensor V h.atom).top =
      (Atom.grayTensorIso V h.atom).hom (V.top, h.atom.top) := by
    rw [← Atom.grayTensorIso_inv_top, Iso.inv_hom_id_apply]
  have hinj : Function.Injective (Atom.grayTensorIso V h.atom).hom :=
    Function.LeftInverse.injective (Iso.hom_inv_id_apply _)
  rw [(Atom.grayTensor V h.atom).mem_bdryFull_top_iff, h.mem_hornSet_iff,
    h.atom.mem_bdryFull_top_iff, V.mem_bdryFull_top_iff, grayTensorLeftFace, htop, hw,
    hinj.ne_iff, hinj.ne_iff, Iso.hom_inv_id_apply]
  set e := Atom.grayTensorIso V h.atom
  by_cases h1 : (e.inv w).1 = V.top
  · rw [← h1]
    exact ⟨fun ⟨h3, h4⟩ => Or.inr ⟨fun h5 => h3 (Prod.ext rfl h5), fun h5 => h4 (Prod.ext rfl h5)⟩,
      fun h3 => h3.elim (fun h4 => absurd rfl h4) fun ⟨h4, h5⟩ =>
        ⟨fun h6 => h4 (congrArg Prod.snd h6), fun h6 => h5 (congrArg Prod.snd h6)⟩⟩
  · exact ⟨fun _ => Or.inl h1, fun _ => ⟨fun h3 => h1 (congrArg Prod.fst h3),
      fun h3 => h1 (congrArg Prod.fst h3)⟩⟩

private theorem mem_faces_grayTensor_top' {A B : Atom} {β : Bool} {z : (Atom.grayTensor A B).ogp} :
    z ∈ (Atom.grayTensor A B).ogp.faces β (Atom.grayTensor A B).top ↔
      ((Atom.grayTensorIso A B).inv z).1 ∈ A.ogp.faces β A.top ∧
          ((Atom.grayTensorIso A B).inv z).2 = B.top ∨
        ((Atom.grayTensorIso A B).inv z).1 = A.top ∧
          ((Atom.grayTensorIso A B).inv z).2 ∈ B.ogp.faces (xor (grade ℕ A.top).bodd β) B.top := by
  set e := Atom.grayTensorIso A B
  have hz : z = e.hom (e.inv z) := (Iso.inv_hom_id_apply e z).symm
  have htop : (Atom.grayTensor A B).top = e.hom (A.top, B.top) := by
    rw [← Atom.grayTensorIso_inv_top, Iso.inv_hom_id_apply]
  rw [hz, htop, (isMorphism e.hom).mem_faces_iff_of_injective
    (Function.LeftInverse.injective (Iso.hom_inv_id_apply e)), mem_faces_grayProduct,
    Iso.hom_inv_id_apply]

theorem mem_targetMarking_grayTensorLeft_iff {w : (Atom.grayTensor V h.atom).ogp} :
    w ∈ (h.grayTensorLeft V marked hV L R M hs hM ht).targetMarking ↔
      ((Atom.grayTensorIso V h.atom).inv w).2 ∈ h.targetMarking ∨
        (marked = true ∧ ((Atom.grayTensorIso V h.atom).inv w).1 = V.top) := by
  have hw : w = (Atom.grayTensorIso V h.atom).hom ((Atom.grayTensorIso V h.atom).inv w) :=
    (Iso.inv_hom_id_apply _ w).symm
  have htop : (Atom.grayTensor V h.atom).top =
      (Atom.grayTensorIso V h.atom).hom (V.top, h.atom.top) := by
    rw [← Atom.grayTensorIso_inv_top, Iso.inv_hom_id_apply]
  have hpair (y : h.atom.ogp) : (Atom.grayTensorIso V h.atom).hom (V.top, y) ∈
      h.grayTensorLeftMarking V marked ↔ y ∈ h.marking ∨ (marked = true ∧ y ∈ h.hornSet) := by
    rw [grayTensorLeftMarking, Set.mem_ofPred_eq, Iso.hom_inv_id_apply]
    refine ⟨fun hy => ?_, fun hy => hy.elim Or.inl fun ⟨hm, hy⟩ => Or.inr (Or.inr ⟨hm, hy, rfl⟩)⟩
    rcases hy with hy | ⟨-, hy⟩ | ⟨hm, hy, -⟩
    · exact Or.inl hy
    · exact absurd rfl ((V.mem_bdryFull_top_iff _).1 hy)
    · exact Or.inr ⟨hm, hy⟩
  have hsign : xor (grade ℕ V.top).bodd (!xor V.dimension.bodd h.side) = !h.side := by
    rw [← V.dimension_eq]
    cases V.dimension.bodd <;> cases h.side <;> rfl
  have hfaces (hy : ∀ y ∈ h.atom.ogp.faces (!h.side) h.atom.top, y ∈ h.marking ∨ marked = true) :
      (Atom.grayTensor V h.atom).ogp.faces (!xor V.dimension.bodd h.side)
          (Atom.grayTensor V h.atom).top ⊆ h.grayTensorLeftMarking V marked := by
    intro z hz
    rcases mem_faces_grayTensor_top'.1 hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h.mem_targetMarking_iff.2 (Or.inl h2),
        (V.mem_bdryFull_top_iff _).2 (mem_faces.1 h1).1.ne⟩)
    · rw [hsign] at h2
      have hz' : z = (Atom.grayTensorIso V h.atom).hom (V.top,
          ((Atom.grayTensorIso V h.atom).inv z).2) :=
        (Iso.inv_hom_id_apply _ z).symm.trans (congrArg _ (Prod.ext h1 rfl))
      rw [hz', hpair]
      refine (hy _ h2).imp_right fun hm => ⟨hm, h.mem_hornSet_iff.2
        ⟨(h.atom.mem_bdryFull_top_iff _).2 (mem_faces.1 h2).1.ne, fun h3 => ?_⟩⟩
      exact Set.disjoint_left.1 (disjoint_faces _ h.side) h.face_mem (h3 ▸ h2)
  refine ⟨fun hw' => ?_, fun hw' => ?_⟩
  · rcases (h.grayTensorLeft V marked hV L R M hs hM ht).mem_targetMarking_iff.1 hw' with
      h1 | ⟨hsub, h1⟩ | h1
    · change w = (Atom.grayTensor V h.atom).top at h1
      rw [h1, Atom.grayTensorIso_inv_top]
      exact Or.inl (h.mem_targetMarking_iff.2 (Or.inl rfl))
    · change w = (Atom.grayTensorIso V h.atom).hom (V.top, h.face) at h1
      rw [h1, Iso.hom_inv_id_apply]
      by_cases hm : marked = true
      · exact Or.inr ⟨hm, rfl⟩
      refine Or.inl (h.mem_targetMarking_iff.2 (Or.inr (Or.inl ⟨fun y hy => ?_, rfl⟩)))
      have hz : (Atom.grayTensorIso V h.atom).hom (V.top, y) ∈ h.grayTensorLeftMarking V marked :=
        hsub (mem_faces_grayTensor_top'.2 (Or.inr (by
        rw [Iso.hom_inv_id_apply]
        refine ⟨rfl, ?_⟩
        change y ∈ h.atom.ogp.faces (xor (grade ℕ V.top).bodd (!xor V.dimension.bodd h.side)) _
        rw [hsign]
        exact hy)))
      exact ((hpair y).1 hz).resolve_right fun h3 => hm h3.1
    · rcases h1 with h1 | ⟨h1, -⟩ | ⟨hm, -, h2⟩
      · exact Or.inl (h.mem_targetMarking_iff.2 (Or.inr (Or.inr h1)))
      · exact Or.inl h1
      · exact Or.inr ⟨hm, h2⟩
  refine (h.grayTensorLeft V marked hV L R M hs hM ht).mem_targetMarking_iff.2 ?_
  rcases hw' with h1 | ⟨hm, h2⟩
  · by_cases h2 : ((Atom.grayTensorIso V h.atom).inv w).1 = V.top
    · rcases h.mem_targetMarking_iff.1 h1 with h3 | ⟨hsub, h3⟩ | h3
      · exact Or.inl (hw.trans ((congrArg _ (Prod.ext h2 h3)).trans htop.symm))
      · exact Or.inr (Or.inl ⟨hfaces fun _ hy => Or.inl (hsub hy),
          hw.trans (congrArg _ (Prod.ext h2 h3))⟩)
      · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, (V.mem_bdryFull_top_iff _).2 h2⟩)))
  · by_cases h3 : ((Atom.grayTensorIso V h.atom).inv w).2 ∈ h.hornSet
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hm, h3, h2⟩)))
    by_cases h4 : ((Atom.grayTensorIso V h.atom).inv w).2 = h.face
    · exact Or.inr (Or.inl ⟨hfaces fun _ _ => Or.inr hm,
        hw.trans (congrArg _ (Prod.ext h2 h4))⟩)
    have h5 : ((Atom.grayTensorIso V h.atom).inv w).2 = h.atom.top := not_not.1 fun h5 =>
      h3 (h.mem_hornSet_iff.2 ⟨(h.atom.mem_bdryFull_top_iff _).2 h5, h4⟩)
    exact Or.inl (hw.trans ((congrArg _ (Prod.ext h2 h5)).trans htop.symm))

end GrayTensorLeft

end MarkedHornData

end Atoms.Shape
