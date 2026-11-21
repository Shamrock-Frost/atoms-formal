import Atoms.Molecule.Construction.DualMap
import Atoms.Molecule.Construction.SuspensionMap
import Atoms.Molecule.Construction.Theta

universe u

open CategoryTheory Order

namespace Atoms.Molecule.OGP

open SuspCarrier

section Restrict

variable {P Q : OGP.{u}}

private theorem restrict_map_iff {C : OGP.{u} → Prop}
    (hC : ∀ {P Q : OGP.{u}}, (P ≅ Q) → C P → C Q) (f : P ⟶ Q) [IsInclusion f]
    (U : LowerSet P) : C (Q.restrict (map f U)) ↔ C (P.restrict U) := by
  obtain ⟨e, -⟩ := exists_iso_restrict_map f U
  exact ⟨hC e.symm, hC e⟩

theorem nonempty_iso_restrict_top (P : OGP.{u}) : Nonempty (P ≅ P.restrict ⊤) :=
  let ⟨e, _⟩ := exists_iso_restrict (𝟙 P) (map_top_of_isIso (𝟙 P))
  ⟨e⟩

private theorem isPasting_of_isPastingIn {X U V : OGP.{u}} {k : ℕ} {A B : LowerSet X}
    (hp : X.IsPastingIn k A B ⊤) (eA : U ≅ X.restrict A) (eB : V ≅ X.restrict B) :
    IsPasting U V k X := by
  refine ⟨eA.hom ≫ incl A, eB.hom ≫ incl B, inferInstance, inferInstance, ?_⟩
  rwa [map_comp, map_comp, map_top_of_isIso eA.hom, map_top_of_isIso eB.hom, map_incl_top,
    map_incl_top]

private theorem IsPastingIn.eq_right_of_krullDim_le {k : ℕ} {V W U : LowerSet P}
    (hp : P.IsPastingIn k V W U) (hV : krullDim V ≤ k) : U = W := by
  rw [← hp.sup_eq, sup_eq_right.2 (hp.le_of_krullDim_le_cond false (A := W) hV)]

private theorem IsPastingIn.eq_left_of_krullDim_le {k : ℕ} {V W U : LowerSet P}
    (hp : P.IsPastingIn k V W U) (hW : krullDim W ≤ k) : U = V := by
  rw [← hp.sup_eq, sup_eq_left.2 (hp.le_of_krullDim_le_cond true (A := V) hW)]

end Restrict

def IsGlobe (P : OGP.{u}) : Prop :=
  ∃ n : ℕ, Nonempty (P ≅ globe.{u} n)

theorem IsGlobe.iso {P Q : OGP.{u}} (e : P ≅ Q) (h : IsGlobe P) : IsGlobe Q :=
  let ⟨n, ⟨f⟩⟩ := h
  ⟨n, ⟨e.symm ≪≫ f⟩⟩

theorem isGlobe_point : IsGlobe point.{u} :=
  ⟨0, ⟨Iso.refl _⟩⟩

theorem IsGlobe.suspension {P : OGP.{u}} (h : IsGlobe P) : IsGlobe (suspension P) :=
  let ⟨n, ⟨e⟩⟩ := h
  ⟨n + 1, ⟨suspension.mapIso e⟩⟩

theorem IsGlobe.isTheta {P : OGP.{u}} (h : IsGlobe P) : IsTheta P :=
  let ⟨n, ⟨e⟩⟩ := h
  .iso e.symm (isTheta_globe n)

section Restrict

variable {P : OGP.{u}}

private theorem isTheta_restrict_Iic_of_isMin {v : P} (hv : IsMin v) :
    IsTheta (P.restrict (LowerSet.Iic v)) :=
  .iso (isoPointRestrictIic hv) .point

private theorem isTheta_restrict_boundary_zero {U : LowerSet P} (hU : IsMoleculeIn P U)
    (α : Bool) : IsTheta (P.restrict (P.boundary U 0 α)) := by
  obtain ⟨v, hv, hUv⟩ := exists_boundary_zero_eq_Iic hU α
  rw [hUv]
  exact isTheta_restrict_Iic_of_isMin hv

theorem IsTheta.restrict_of_isPastingIn_zero {V W U : LowerSet P} (hp : P.IsPastingIn 0 V W U)
    (hV : IsTheta (P.restrict V)) (hW : IsTheta (P.restrict W)) : IsTheta (P.restrict U) := by
  rcases le_or_gt (krullDim V) ((0 : ℕ) : WithBot ℕ∞) with hV0 | hV0
  · rwa [hp.eq_right_of_krullDim_le hV0]
  rcases le_or_gt (krullDim W) ((0 : ℕ) : WithBot ℕ∞) with hW0 | hW0
  · rwa [hp.eq_left_of_krullDim_le hW0]
  obtain ⟨i, j, hi, hj, hp'⟩ := hp.isPasting_restrict
  obtain ⟨ψ, -, -⟩ := hp'.exists_isPushout
  obtain ⟨e⟩ := (isPasting_glue _ _ 0 ψ).nonempty_iso hV.isMolecule ⟨i, j, hi, hj, hp'⟩
  exact .iso e (.wedge ψ hV hW (lt_min hV0 hW0))

end Restrict

theorem IsTheta.boundary {P : OGP.{u}} (h : IsTheta P) (n : ℕ) (α : Bool) :
    IsTheta (P.restrict (P.boundary ⊤ n α)) := by
  rcases n with _ | m
  · exact isTheta_restrict_boundary_zero h.isMolecule α
  induction h generalizing m with
  | point =>
    rw [← LowerSet.Iic_top, boundary_Iic_of_isMin (isMin_point _)]
    exact isTheta_restrict_Iic_of_isMin (isMin_point _)
  | iso e _ ih =>
    rw [← map_top_of_isIso e.hom, ← map_boundary]
    exact (restrict_map_iff (fun e h => IsTheta.iso e h) e.hom _).2 (ih m)
  | @suspend Y hY ih =>
    rw [← susp_top, boundary_susp_succ (hY.isMolecule.boundary m α).nonempty]
    obtain ⟨e⟩ := nonempty_suspension_restrict_iso (Y.boundary ⊤ m α)
    refine .iso e (.suspend ?_)
    rcases m with _ | m
    · exact isTheta_restrict_boundary_zero hY.isMolecule α
    · exact ih m
  | wedge φ hP hQ _ ihP ihQ =>
    have hb := (isPastingIn_glue _ _ 0 φ).boundary_of_lt
      (isMoleculeIn_map _ hP.isMolecule).isGlobular (isMoleculeIn_map _ hQ.isMolecule).isGlobular
      (Nat.succ_pos m) α
    rw [← map_boundary, ← map_boundary] at hb
    exact .restrict_of_isPastingIn_zero hb
      ((restrict_map_iff (fun e h => IsTheta.iso e h) _ _).2 (ihP m))
      ((restrict_map_iff (fun e h => IsTheta.iso e h) _ _).2 (ihQ m))

theorem IsTheta.isGlobe_Iic {P : OGP.{u}} (h : IsTheta P) (x : P) :
    IsGlobe (P.restrict (LowerSet.Iic x)) := by
  induction h with
  | point => exact .iso (isoPointRestrictIic (isMin_point x)) isGlobe_point
  | iso e _ ih =>
    have h := (restrict_map_iff (fun e h => IsGlobe.iso e h) e.hom _).2 (ih (e.inv x))
    rwa [map_Iic, Iso.inv_hom_id_apply] at h
  | suspend _ ih =>
    cases x with
    | pole α => exact .iso (isoPointRestrictIic (isMin_pole α)) isGlobe_point
    | susp y =>
      rw [← susp_Iic]
      obtain ⟨e⟩ := nonempty_suspension_restrict_iso (LowerSet.Iic y)
      exact .iso e (ih y).suspension
  | wedge φ _ _ _ ihP ihQ =>
    rcases glue.exists_inl_or_inr x with ⟨p, rfl⟩ | ⟨q, rfl⟩
    · rw [← map_Iic]
      exact (restrict_map_iff (fun e h => IsGlobe.iso e h) _ _).2 (ihP p)
    · rw [← map_Iic]
      exact (restrict_map_iff (fun e h => IsGlobe.iso e h) _ _).2 (ihQ q)

theorem IsGlobe.isGlobe_Iic {P : OGP.{u}} (h : IsGlobe P) (x : P) :
    IsGlobe (P.restrict (LowerSet.Iic x)) :=
  h.isTheta.isGlobe_Iic x

private theorem IsTheta.finite {P : OGP.{u}} (h : IsTheta P) : Finite P :=
  Set.finite_univ_iff.1 (by simpa using h.isMolecule.finite)

private theorem card_vertices_suspension (P : OGP.{u}) :
    Nat.card {x : suspension P // grade ℕ x = 0} = 2 := by
  have hb : Function.Bijective fun b : Bool => (⟨pole b, grade_pole b⟩ :
      {x : suspension P // grade ℕ x = 0}) := by
    refine ⟨fun a b h => pole.inj (congrArg Subtype.val h), fun ⟨x, hx⟩ => ?_⟩
    cases x with
    | pole b => exact ⟨b, rfl⟩
    | susp y => exact absurd hx (by simp)
  rw [← Nat.card_congr (Equiv.ofBijective _ hb), Nat.card_eq_fintype_card, Fintype.card_bool]

theorem card_vertices_theta (ts : List PlaneTree) :
    Nat.card {x : theta.{u} (.node ts) // grade ℕ x = 0} = ts.length + 1 := by
  induction ts with
  | nil =>
    rw [List.length_nil, zero_add, Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun _ _ => Subtype.ext rfl⟩, ⟨⟨PUnit.unit, grade_eq_zero_iff.2 (isMin_point _)⟩⟩⟩
  | cons t ts ih =>
    rcases ts with _ | ⟨s, ss⟩
    · exact card_vertices_suspension _
    rw [List.length_cons, theta_node_cons_cons]
    set A := (PlaneTree.thetaData.{u} t).susp
    set B := PlaneTree.thetaData.{u} (.node (s :: ss))
    set φ := VertexedMolecule.pastingIso A B
    have : Finite B.ogp := (isTheta_theta _).finite
    have hsrc (h : A.src ∈ A.ogp.boundary ⊤ 0 true) : False := by
      rw [A.boundary_true, LowerSet.mem_Iic_iff] at h
      exact absurd (pole_le_pole.1 h) Bool.false_ne_true
    let f : Option {y : B.ogp // grade ℕ y = 0} → {x : glue φ // grade ℕ x = 0} :=
      fun o => o.elim ⟨glue.inl φ A.src, ((isMorphism _).grade_eq _).trans (grade_pole false)⟩
        fun y => ⟨glue.inr φ y, ((isMorphism _).grade_eq _).trans y.2⟩
    have hf : Function.Bijective f := by
      refine ⟨?_, fun ⟨x, hx⟩ => ?_⟩
      · intro o o' h
        cases o with
        | none =>
          cases o' with
          | none => rfl
          | some y => exact (hsrc (glue.inl_eq_inr_iff.1 (congrArg Subtype.val h)).1).elim
        | some y =>
          cases o' with
          | none => exact (hsrc (glue.inl_eq_inr_iff.1 (congrArg Subtype.val h).symm).1).elim
          | some y' =>
            exact congrArg some (Subtype.ext (IsInclusion.injective (congrArg Subtype.val h)))
      rcases glue.exists_inl_or_inr x with ⟨p, rfl⟩ | ⟨q, rfl⟩
      · rw [(isMorphism _).grade_eq] at hx
        cases p with
        | susp y => exact absurd hx (ne_of_eq_of_ne (grade_susp y) (Nat.succ_ne_zero _))
        | pole β =>
          cases β
          · exact ⟨none, rfl⟩
          · have hp : (pole true : A.ogp) ∈ A.ogp.boundary ⊤ 0 true := by
              rw [A.boundary_true]
              exact LowerSet.mem_Iic_iff.2 le_rfl
            refine ⟨some ⟨φ.hom ⟨_, hp⟩, ?_⟩, Subtype.ext (glue.inl_eq_inr_iff.2 ⟨hp, rfl⟩).symm⟩
            rw [← (isMorphism (glue.inr φ)).grade_eq, ← (glue.inl_eq_inr_iff.2 ⟨hp, rfl⟩)]
            exact hx
      · exact ⟨some ⟨q, (isMorphism _).grade_eq q ▸ hx⟩, rfl⟩
    have := Fintype.ofFinite {y : B.ogp // grade ℕ y = 0}
    rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_option,
      ← Nat.card_eq_fintype_card]
    exact congrArg (· + 1) ih

section HeadSplit

variable {P : OGP.{u}}

private structure IsSuspLike (A : LowerSet P) (v c : P) : Prop where
  le_of_not_le : ∀ z ∈ A, ¬ v ≤ z → z ≤ c
  le_of_lt : ∀ w ∈ A, v < w → c ≤ w
  exists_lt : ∃ w ∈ A, v < w
  not_le : ¬ v ≤ c

private theorem isSuspLike_suspension (Y : OGP.{u}) [Nonempty Y] :
    IsSuspLike (⊤ : LowerSet (suspension Y)) (pole false) (pole true) where
  le_of_not_le z _ h := by
    cases z with
    | pole β =>
      cases β
      · exact absurd le_rfl h
      · exact le_rfl
    | susp y => exact absurd (pole_le_susp false y) h
  le_of_lt w _ h := by
    cases w with
    | pole β => exact absurd h (isMin_pole β).not_lt
    | susp y => exact pole_le_susp true y
  exists_lt := ⟨susp (Classical.arbitrary Y), trivial, pole_lt_susp false _⟩
  not_le := by simp

private theorem IsSuspLike.map {Q : OGP.{u}} (f : P ⟶ Q) [IsInclusion f] {A : LowerSet P}
    {v c : P} (h : IsSuspLike A v c) : IsSuspLike (map f A) (f v) (f c) where
  le_of_not_le := by
    rintro _ ⟨z, hz, rfl⟩ hvz
    exact (isMorphism f).monotone (h.le_of_not_le z hz fun h' => hvz ((isMorphism f).monotone h'))
  le_of_lt := by
    rintro _ ⟨w, hw, rfl⟩ hvw
    exact (isMorphism f).monotone (h.le_of_lt w hw
      (lt_of_le_of_ne ((IsInclusion.le_iff f).1 hvw.le) fun e => hvw.ne (congrArg f e)))
  exists_lt := by
    obtain ⟨w, hw, hvw⟩ := h.exists_lt
    exact ⟨f w, ⟨w, hw, rfl⟩, lt_of_le_of_ne ((isMorphism f).monotone hvw.le)
      fun e => hvw.ne (IsInclusion.injective e)⟩
  not_le hvc := h.not_le ((IsInclusion.le_iff f).1 hvc)

private theorem IsSuspLike.exists_le_lt {A : LowerSet P} {v c : P} (h : IsSuspLike A v c)
    {z : P} (hz : z ∈ A) : ∃ w ∈ A, z ≤ w ∧ v < w := by
  by_cases hvz : v ≤ z
  · rcases hvz.lt_or_eq with hvz | rfl
    · exact ⟨z, hz, le_rfl, hvz⟩
    · obtain ⟨w, hw, hvw⟩ := h.exists_lt
      exact ⟨w, hw, hvw.le, hvw⟩
  · obtain ⟨w, hw, hvw⟩ := h.exists_lt
    exact ⟨w, hw, (h.le_of_not_le z hz hvz).trans (h.le_of_lt w hw hvw), hvw⟩

private structure IsHeadSplit (U A R : LowerSet P) (v c : P) : Prop where
  isPastingIn : P.IsPastingIn 0 A R U
  boundary_eq : P.boundary U 0 false = LowerSet.Iic v
  inf_eq : A ⊓ R = LowerSet.Iic c
  isSuspLike : IsSuspLike A v c
  isMoleculeIn_left : IsMoleculeIn P A
  isMoleculeIn_right : IsMoleculeIn P R

namespace IsHeadSplit

variable {U A R : LowerSet P} {v c : P}

private theorem mem_left (h : IsHeadSplit U A R v c) : v ∈ A := by
  have hv : v ∈ P.boundary U 0 false := h.boundary_eq ▸ LowerSet.mem_Iic_iff.2 le_rfl
  rw [h.isPastingIn.boundary_input] at hv
  exact boundary_le A 0 false hv

private theorem notMem_right (h : IsHeadSplit U A R v c) : v ∉ R := fun hv =>
  h.isSuspLike.not_le (LowerSet.mem_Iic_iff.1 (h.inf_eq ▸ ⟨h.mem_left, hv⟩))

private theorem left_eq (h : IsHeadSplit U A R v c) :
    A = lowerClosure {w | w ∈ U ∧ v < w} := by
  refine le_antisymm (fun z hz => ?_) (lowerClosure_le.2 fun w ⟨hw, hvw⟩ => ?_)
  · obtain ⟨w, hw, hzw, hvw⟩ := h.isSuspLike.exists_le_lt hz
    exact mem_lowerClosure.2 ⟨w, ⟨h.isPastingIn.left_le hw, hvw⟩, hzw⟩
  · rw [← h.isPastingIn.sup_eq] at hw
    exact hw.resolve_right fun hwR => h.notMem_right (R.lower hvw.le hwR)

private theorem coe_right_eq (h : IsHeadSplit U A R v c) :
    (R : Set P) = {z | z ∈ U ∧ ¬ v ≤ z} := by
  refine Set.ext fun z => ⟨fun hz => ⟨h.isPastingIn.right_le hz,
    fun hvz => h.notMem_right (R.lower hvz hz)⟩, fun ⟨hz, hvz⟩ => ?_⟩
  rw [← h.isPastingIn.sup_eq] at hz
  refine hz.elim (fun hzA => ?_) id
  have hc : c ∈ A ⊓ R := h.inf_eq ▸ LowerSet.mem_Iic_iff.2 le_rfl
  exact R.lower (h.isSuspLike.le_of_not_le z hzA hvz) hc.2

private theorem vertex_eq {A' R' : LowerSet P} {v' c' : P} (h : IsHeadSplit U A R v c)
    (h' : IsHeadSplit U A' R' v' c') : v = v' := by
  have hI := h.boundary_eq.symm.trans h'.boundary_eq
  exact le_antisymm (LowerSet.mem_Iic_iff.1 (hI ▸ LowerSet.mem_Iic_iff.2 le_rfl))
    (LowerSet.mem_Iic_iff.1 (hI.symm ▸ LowerSet.mem_Iic_iff.2 le_rfl))

private theorem left_eq_left {A' R' : LowerSet P} {v' c' : P} (h : IsHeadSplit U A R v c)
    (h' : IsHeadSplit U A' R' v' c') : A = A' := by
  rw [h.left_eq, h'.left_eq, h.vertex_eq h']

private theorem right_eq_right {A' R' : LowerSet P} {v' c' : P} (h : IsHeadSplit U A R v c)
    (h' : IsHeadSplit U A' R' v' c') : R = R' :=
  SetLike.coe_injective (by rw [h.coe_right_eq, h'.coe_right_eq, h.vertex_eq h'])

private theorem map {Q : OGP.{u}} (f : P ⟶ Q) [IsInclusion f] (h : IsHeadSplit U A R v c) :
    IsHeadSplit (map f U) (map f A) (map f R) (f v) (f c) where
  isPastingIn := (isPastingIn_map_iff f 0 A R U).2 h.isPastingIn
  boundary_eq := by rw [← map_boundary, h.boundary_eq, map_Iic]
  inf_eq := by rw [← map_inf, h.inf_eq, map_Iic]
  isSuspLike := h.isSuspLike.map f
  isMoleculeIn_left := isMoleculeIn_map f h.isMoleculeIn_left
  isMoleculeIn_right := isMoleculeIn_map f h.isMoleculeIn_right

private theorem boundary (h : IsHeadSplit U A R v c) {n : ℕ} (hn : 0 < n) (α : Bool) :
    IsHeadSplit (P.boundary U n α) (P.boundary A n α) (P.boundary R n α) v c where
  isPastingIn := h.isPastingIn.boundary_of_lt h.isMoleculeIn_left.isGlobular
    h.isMoleculeIn_right.isGlobular hn α
  boundary_eq := by
    rw [(h.isPastingIn.isMoleculeIn h.isMoleculeIn_left h.isMoleculeIn_right).isGlobular
      |>.boundary_boundary_eq_of_le hn.le (Or.inl hn), h.boundary_eq]
  inf_eq := by
    rw [(h.isPastingIn.boundary_of_lt h.isMoleculeIn_left.isGlobular
      h.isMoleculeIn_right.isGlobular hn α).inf_eq_output,
      h.isMoleculeIn_left.isGlobular.boundary_boundary_eq_of_le hn.le (Or.inl hn),
      ← h.isPastingIn.inf_eq_output, h.inf_eq]
  isSuspLike :=
    { le_of_not_le := fun z hz => h.isSuspLike.le_of_not_le z (boundary_le A n α hz)
      le_of_lt := fun w hw => h.isSuspLike.le_of_lt w (boundary_le A n α hw)
      exists_lt := by
        rcases le_or_gt (krullDim A) n with hle | hlt
        · rw [boundary_eq_self hle]
          exact h.isSuspLike.exists_lt
        obtain ⟨⟨w, hw⟩, hwn⟩ := exists_grade_eq_of_krullDim_eq
          (h.isMoleculeIn_left.krullDim_boundary hlt.le α)
        have hwn' : grade ℕ w = n := hwn
        have hc : grade ℕ c ≤ 0 := grade_le_of_mem_boundary
          (h.isPastingIn.inf_eq_output ▸ h.inf_eq ▸ LowerSet.mem_Iic_iff.2 le_rfl :
            c ∈ P.boundary A 0 true)
        have hv : grade ℕ v ≤ 0 := grade_le_of_mem_boundary
          (h.boundary_eq ▸ LowerSet.mem_Iic_iff.2 le_rfl : v ∈ P.boundary U 0 false)
        have hvw : v ≤ w := by
          by_contra hvw
          have := (grade_strictMono (𝕆 := ℕ)).monotone
            (h.isSuspLike.le_of_not_le w (boundary_le A n α hw) hvw)
          omega
        exact ⟨w, hw, lt_of_le_of_ne hvw fun e => by subst e; omega⟩
      not_le := h.isSuspLike.not_le }
  isMoleculeIn_left := h.isMoleculeIn_left.boundary n α
  isMoleculeIn_right := h.isMoleculeIn_right.boundary n α

end IsHeadSplit

private theorem nonempty_restrict_top_iso {X Y : OGP.{u}} (e : X ≅ Y) :
    Nonempty (X.restrict ⊤ ≅ Y) :=
  let ⟨f⟩ := nonempty_iso_restrict_top X
  ⟨f.symm ≪≫ e⟩

private theorem exists_isHeadSplit_theta (t : PlaneTree) (ts : List PlaneTree) :
    ∃ (A R : LowerSet (theta.{u} (.node (t :: ts)))) (v c : theta.{u} (.node (t :: ts))),
      IsHeadSplit ⊤ A R v c ∧
      Nonempty ((theta (.node (t :: ts))).restrict A ≅ suspension (theta t)) ∧
      Nonempty ((theta (.node (t :: ts))).restrict R ≅ theta (.node ts)) := by
  have : Nonempty (theta.{u} t) := ⟨(isTheta_theta t).isMolecule.nonempty.some⟩
  rcases ts with _ | ⟨s, ss⟩
  · rw [theta_node_singleton]
    have hb (α : Bool) : (suspension (theta.{u} t)).boundary ⊤ 0 α = LowerSet.Iic (pole α) := by
      rw [← susp_top, boundary_susp_zero (isTheta_theta t).isMolecule.nonempty]
    refine ⟨⊤, LowerSet.Iic (pole true), pole false, pole true, ⟨?_, hb false, top_inf_eq _,
      isSuspLike_suspension _, isMolecule_suspension _ (isTheta_theta t).isMolecule,
      .point _ (isMin_pole true)⟩, nonempty_restrict_top_iso (Iso.refl _),
      ⟨(isoPointRestrictIic (isMin_pole true)).symm⟩⟩
    rw [← hb true]
    exact isPastingIn_self_boundary_true ⊤ 0
  · rw [theta_node_cons_cons]
    set A := (PlaneTree.thetaData.{u} t).susp
    set B := PlaneTree.thetaData.{u} (.node (s :: ss))
    set φ := VertexedMolecule.pastingIso A B
    obtain ⟨eA, -⟩ := exists_iso_restrict_map (glue.inl φ) ⊤
    obtain ⟨eB, -⟩ := exists_iso_restrict_map (glue.inr φ) ⊤
    obtain ⟨fA⟩ := nonempty_iso_restrict_top A.ogp
    obtain ⟨fB⟩ := nonempty_iso_restrict_top B.ogp
    refine ⟨map (glue.inl φ) ⊤, map (glue.inr φ) ⊤, glue.inl φ A.src, glue.inl φ A.tgt,
      ⟨isPastingIn_glue _ _ 0 φ,
        boundary_zero_false_glue φ A.isMolecule B.isMolecule A.boundary_false, ?_,
        (isSuspLike_suspension (theta t)).map (glue.inl φ), isMoleculeIn_map _ A.isMolecule,
        isMoleculeIn_map _ B.isMolecule⟩,
      ⟨eA.symm ≪≫ fA.symm⟩, ⟨eB.symm ≪≫ fB.symm⟩⟩
    rw [glue.map_inl_inf_map_inr, map_comp, map_incl_top, ← map_Iic]
    exact congrArg (map (glue.inl φ)) A.boundary_true

private theorem exists_isHeadSplit_of_iso {P : OGP.{u}} {U : LowerSet P} {t : PlaneTree}
    {ts : List PlaneTree} (e : theta.{u} (.node (t :: ts)) ≅ P.restrict U) :
    ∃ (A R : LowerSet P) (v c : P), IsHeadSplit U A R v c ∧
      Nonempty (P.restrict A ≅ suspension (theta t)) ∧
      Nonempty (P.restrict R ≅ theta (.node ts)) := by
  obtain ⟨A, R, v, c, h, ⟨eA⟩, ⟨eR⟩⟩ := exists_isHeadSplit_theta t ts
  have hU : map (e.hom ≫ incl U) ⊤ = U := by rw [map_comp, map_top_of_isIso, map_incl_top]
  obtain ⟨fA, -⟩ := exists_iso_restrict_map (e.hom ≫ incl U) A
  obtain ⟨fR, -⟩ := exists_iso_restrict_map (e.hom ≫ incl U) R
  exact ⟨_, _, _, _, hU ▸ h.map (e.hom ≫ incl U), ⟨fA.symm ≪≫ eA⟩, ⟨fR.symm ≪≫ eR⟩⟩

private theorem krullDim_eq_of_iso {X Y : OGP.{u}} (e : X ≅ Y) : krullDim X = krullDim Y :=
  Order.krullDim_eq_of_orderIso (orderIsoOfIso e)

private theorem krullDim_theta_node_nil : krullDim (theta.{u} (.node [])) = 0 :=
  (krullDim_theta _).trans rfl

private theorem krullDim_theta_node_cons_pos (t : PlaneTree) (ts : List PlaneTree) :
    0 < krullDim (theta.{u} (.node (t :: ts))) := by
  rw [krullDim_theta]
  exact_mod_cast lt_of_lt_of_le (Nat.succ_pos _) (le_max_left _ _)

namespace PlaneTree

mutual

private theorem eq_of_nonempty_iso_theta :
    (t t' : PlaneTree) → Nonempty (theta.{u} t ≅ theta.{u} t') → t = t'
  | node ts, node ts', h => congrArg node (eq_of_nonempty_iso_thetaNode ts ts' h)

private theorem eq_of_nonempty_iso_thetaNode :
    (ts ts' : List PlaneTree) → Nonempty (theta.{u} (node ts) ≅ theta.{u} (node ts')) → ts = ts'
  | [], [], _ => rfl
  | [], b :: bs, ⟨e⟩ => absurd (krullDim_theta_node_cons_pos.{u} b bs)
    (by rw [← krullDim_eq_of_iso e, krullDim_theta_node_nil]; exact lt_irrefl 0)
  | a :: as, [], ⟨e⟩ => absurd (krullDim_theta_node_cons_pos.{u} a as)
    (by rw [krullDim_eq_of_iso e, krullDim_theta_node_nil]; exact lt_irrefl 0)
  | a :: as, b :: bs, ⟨e⟩ => by
    obtain ⟨f⟩ := nonempty_iso_restrict_top (theta.{u} (node (b :: bs)))
    obtain ⟨A, R, v, c, h, ⟨eA⟩, ⟨eR⟩⟩ := exists_isHeadSplit_of_iso (e ≪≫ f)
    obtain ⟨A', R', v', c', h', ⟨eA'⟩, ⟨eR'⟩⟩ := exists_isHeadSplit_of_iso f
    obtain rfl := h.left_eq_left h'
    obtain rfl := h.right_eq_right h'
    have : Nonempty (theta.{u} a) := ⟨(isTheta_theta a).isMolecule.nonempty.some⟩
    rw [eq_of_nonempty_iso_theta a b ⟨suspension.desuspIso (eA.symm ≪≫ eA')⟩,
      eq_of_nonempty_iso_thetaNode as bs ⟨eR.symm ≪≫ eR'⟩]

end

theorem eq_of_nonempty_iso {t t' : PlaneTree} (h : Nonempty (theta.{u} t ≅ theta.{u} t')) :
    t = t' :=
  eq_of_nonempty_iso_theta t t' h

end PlaneTree

private theorem isPasting_theta_cons_cons (t s : PlaneTree) (ss : List PlaneTree) :
    IsPasting (suspension (theta.{u} t)) (theta.{u} (.node (s :: ss))) 0
      (theta.{u} (.node (t :: s :: ss))) := by
  rw [theta_node_cons_cons]
  exact isPasting_glue _ _ 0 _

private theorem IsPasting.of_iso_left_right {U V U' V' W : OGP.{u}} {k : ℕ}
    (h : IsPasting U V k W) (eU : U' ≅ U) (eV : V' ≅ V) : IsPasting U' V' k W := by
  obtain ⟨i, j, _, _, hp⟩ := h
  refine ⟨eU.hom ≫ i, eV.hom ≫ j, inferInstance, inferInstance, ?_⟩
  rwa [map_comp, map_comp, map_top_of_isIso eU.hom, map_top_of_isIso eV.hom]

theorem isPasting_theta_append {ts ss : List PlaneTree} (hts : ts ≠ []) (hss : ss ≠ []) :
    IsPasting (theta.{u} (.node ts)) (theta.{u} (.node ss)) 0 (theta.{u} (.node (ts ++ ss))) := by
  obtain ⟨s, ss, rfl⟩ := List.exists_cons_of_ne_nil hss
  induction ts with
  | nil => exact absurd rfl hts
  | cons a ts ih =>
    rcases ts with _ | ⟨b, bs⟩
    · exact isPasting_theta_cons_cons a s ss
    have ih := ih (List.cons_ne_nil b bs)
    rw [List.cons_append] at ih
    rw [List.cons_append, List.cons_append]
    obtain ⟨i, j, _, _, hM⟩ := ih
    obtain ⟨i₀, j₀, _, _, hX⟩ := isPasting_theta_cons_cons.{u} a b (bs ++ s :: ss)
    have hB : (theta.{u} (.node (a :: b :: (bs ++ s :: ss)))).IsPastingIn 0
        (map (i ≫ j₀) ⊤) (map (j ≫ j₀) ⊤) (map j₀ ⊤) := by
      rw [map_comp, map_comp]
      exact (isPastingIn_map_iff j₀ 0 _ _ ⊤).2 hM
    have hAN := hB.isPastingIn_left_sup hX
    obtain ⟨eA, -⟩ := exists_iso_restrict_map i₀ ⊤
    obtain ⟨eN, -⟩ := exists_iso_restrict_map (i ≫ j₀) ⊤
    obtain ⟨eT, -⟩ := exists_iso_restrict_map (j ≫ j₀) ⊤
    obtain ⟨fA⟩ := nonempty_iso_restrict_top (suspension (theta.{u} a))
    obtain ⟨fN⟩ := nonempty_iso_restrict_top (theta.{u} (.node (b :: bs)))
    obtain ⟨fT⟩ := nonempty_iso_restrict_top (theta.{u} (.node (s :: ss)))
    obtain ⟨e⟩ := (isPasting_theta_cons_cons.{u} a b bs).nonempty_iso
      (isTheta_theta (.node [a])).isMolecule
      (hAN.isPasting_restrict.of_iso_left_right (fA ≪≫ eA) (fN ≪≫ eN))
    exact isPasting_of_isPastingIn (hB.assoc_symm hX) e (fT ≪≫ eT)

private theorem IsTheta.exists_iso {P : OGP.{u}} (h : IsTheta P) :
    ∃ t : PlaneTree, Nonempty (P ≅ theta.{u} t) := by
  induction h with
  | point => exact ⟨.node [], ⟨Iso.refl _⟩⟩
  | iso e _ ih =>
    obtain ⟨t, ⟨f⟩⟩ := ih
    exact ⟨t, ⟨e.symm ≪≫ f⟩⟩
  | suspend _ ih =>
    obtain ⟨t, ⟨f⟩⟩ := ih
    exact ⟨.node [t], ⟨suspension.mapIso f⟩⟩
  | wedge φ hP _ hd ihP ihQ =>
    obtain ⟨⟨ts⟩, ⟨eP⟩⟩ := ihP
    obtain ⟨⟨ss⟩, ⟨eQ⟩⟩ := ihQ
    have hne {X : OGP.{u}} {us : List PlaneTree} (e : X ≅ theta.{u} (.node us))
        (hX : 0 < krullDim X) : us ≠ [] := by
      rintro rfl
      rw [krullDim_eq_of_iso e, krullDim_theta_node_nil] at hX
      exact lt_irrefl 0 hX
    obtain ⟨e⟩ := ((isPasting_glue _ _ 0 φ).of_iso_left_right eP.symm eQ.symm).nonempty_iso
      (isTheta_theta _).isMolecule
      (isPasting_theta_append (hne eP (lt_min_iff.1 hd).1) (hne eQ (lt_min_iff.1 hd).2))
    exact ⟨.node (ts ++ ss), ⟨e⟩⟩

theorem IsTheta.existsUnique_iso {P : OGP.{u}} (h : IsTheta P) :
    ∃! t : PlaneTree, Nonempty (P ≅ theta.{u} t) :=
  let ⟨t, ⟨e⟩⟩ := h.exists_iso
  ⟨t, ⟨e⟩, fun _ ⟨e'⟩ => PlaneTree.eq_of_nonempty_iso ⟨e'.symm ≪≫ e⟩⟩

theorem isTheta_iff_exists_iso {P : OGP.{u}} :
    IsTheta P ↔ ∃ t : PlaneTree, Nonempty (P ≅ theta.{u} t) :=
  ⟨IsTheta.exists_iso, fun ⟨t, ⟨e⟩⟩ => .iso e.symm (isTheta_theta t)⟩

end HeadSplit

section Paste

variable {P : OGP.{u}}

private theorem isTheta_restrict_of_isPastingIn_suspension {k : ℕ}
    (ih : ∀ {X : OGP.{u}} {V W U : LowerSet X}, X.IsPastingIn k V W U →
      IsTheta (X.restrict V) → IsTheta (X.restrict W) → IsTheta (X.restrict U))
    {A A' D : LowerSet P} (hp : P.IsPastingIn (k + 1) A A' D) {Y Y' : OGP.{u}} (hY : IsTheta Y)
    (hY' : IsTheta Y') (eA : P.restrict A ≅ suspension Y) (eA' : P.restrict A' ≅ suspension Y') :
    IsTheta (P.restrict D) := by
  obtain ⟨i, j, hi, hj, hp'⟩ := hp.isPasting_restrict.of_iso_left_right eA.symm eA'.symm
  obtain ⟨ψ, -, -⟩ := hp'.exists_isPushout
  have hb : (suspension Y).boundary ⊤ (k + 1) true = (Y.boundary ⊤ k true).susp := by
    rw [← susp_top, boundary_susp_succ (hY.isMolecule.boundary k true).nonempty]
  have hb' : (suspension Y').boundary ⊤ (k + 1) false = (Y'.boundary ⊤ k false).susp := by
    rw [← susp_top, boundary_susp_succ (hY'.isMolecule.boundary k false).nonempty]
  obtain ⟨s⟩ := nonempty_suspension_restrict_iso (Y.boundary ⊤ k true)
  obtain ⟨s'⟩ := nonempty_suspension_restrict_iso (Y'.boundary ⊤ k false)
  have : Nonempty (Y.restrict (Y.boundary ⊤ k true)) :=
    ⟨⟨_, (hY.isMolecule.boundary k true).nonempty.some_mem⟩⟩
  let ψ' : PastingIso Y Y' k := suspension.desuspIso
    (s ≪≫ restrictCongr hb.symm ≪≫ ψ ≪≫ restrictCongr hb' ≪≫ s'.symm)
  obtain ⟨fY⟩ := nonempty_iso_restrict_top Y
  obtain ⟨fY'⟩ := nonempty_iso_restrict_top Y'
  obtain ⟨fG⟩ := nonempty_iso_restrict_top (glue ψ')
  obtain ⟨gY, -⟩ := exists_iso_restrict_map (glue.inl ψ') ⊤
  obtain ⟨gY', -⟩ := exists_iso_restrict_map (glue.inr ψ') ⊤
  have hG : IsTheta (glue ψ') := .iso fG.symm (ih (isPastingIn_glue Y Y' k ψ')
    (.iso (fY ≪≫ gY) hY) (.iso (fY' ≪≫ gY') hY'))
  have hne : ((map (glue.inl ψ') ⊤ ⊓ map (glue.inr ψ') ⊤ : LowerSet (glue ψ')) :
      Set (glue ψ')).Nonempty := by
    rw [(isPastingIn_glue Y Y' k ψ').inf_eq_output, ← map_boundary]
    exact (isMoleculeIn_map _ (hY.isMolecule.boundary k true)).nonempty
  have hS := isPastingIn_susp (isPastingIn_glue Y Y' k ψ') hne
  rw [susp_top] at hS
  obtain ⟨t⟩ := nonempty_suspension_restrict_iso (map (glue.inl ψ') ⊤)
  obtain ⟨t'⟩ := nonempty_suspension_restrict_iso (map (glue.inr ψ') ⊤)
  obtain ⟨e⟩ := (isPasting_of_isPastingIn hS (suspension.mapIso (fY ≪≫ gY) ≪≫ t)
    (suspension.mapIso (fY' ≪≫ gY') ≪≫ t')).nonempty_iso
    (isMolecule_suspension _ hY.isMolecule) ⟨i, j, hi, hj, hp'⟩
  exact .iso e (.suspend hG)

private theorem IsHeadSplit.isPastingIn_interchange {k : ℕ} {V W D A R A' R' : LowerSet P}
    {v c v' c' : P} (hp : P.IsPastingIn (k + 1) V W D) (hs : IsHeadSplit V A R v c)
    (hs' : IsHeadSplit W A' R' v' c')
    (hA : P.boundary A (k + 1) true = P.boundary A' (k + 1) false)
    (hR : P.boundary R (k + 1) true = P.boundary R' (k + 1) false) :
    P.IsPastingIn (k + 1) A A' (A ⊔ A') ∧ P.IsPastingIn (k + 1) R R' (R ⊔ R') ∧
      P.IsPastingIn 0 (A ⊔ A') (R ⊔ R') D := by
  have hb := hs.boundary (Nat.succ_pos k) true
  have hb' := hs'.boundary (Nat.succ_pos k) false
  rw [← hp.inf_eq_output] at hb
  rw [← hp.inf_eq_input, ← hA, ← hR] at hb'
  have hc : c' = c := by
    have hI := hb'.inf_eq.symm.trans hb.inf_eq
    exact le_antisymm (LowerSet.mem_Iic_iff.1 (hI ▸ LowerSet.mem_Iic_iff.2 le_rfl))
      (LowerSet.mem_Iic_iff.1 (hI.symm ▸ LowerSet.mem_Iic_iff.2 le_rfl))
  subst hc
  have hcXY : c' ∈ P.boundary A (k + 1) true ⊓ P.boundary R (k + 1) true :=
    hb.inf_eq ▸ LowerSet.mem_Iic_iff.2 le_rfl
  have hXA' : P.boundary A (k + 1) true ≤ A' := hA ▸ boundary_le _ _ _
  have hYR' : P.boundary R (k + 1) true ≤ R' := hR ▸ boundary_le _ _ _
  have hVW {z : P} (hzV : z ∈ V) (hzW : z ∈ W) :
      z ∈ P.boundary A (k + 1) true ∨ z ∈ P.boundary R (k + 1) true := by
    rw [← LowerSet.mem_sup_iff, hb.isPastingIn.sup_eq]
    exact ⟨hzV, hzW⟩
  have hAR {z : P} (hzA : z ∈ A) (hzR : z ∈ R) : z ≤ c' :=
    LowerSet.mem_Iic_iff.1 (hs.inf_eq ▸ ⟨hzA, hzR⟩)
  have hAR' {z : P} (hzA : z ∈ A') (hzR : z ∈ R') : z ≤ c' :=
    LowerSet.mem_Iic_iff.1 (hs'.inf_eq ▸ ⟨hzA, hzR⟩)
  have hAA : A ⊓ A' = P.boundary A (k + 1) true := by
    refine le_antisymm (fun z ⟨hzA, hzA'⟩ => ?_) (le_inf (boundary_le _ _ _) hXA')
    exact (hVW (hs.isPastingIn.left_le hzA) (hs'.isPastingIn.left_le hzA')).elim id
      fun hzY => LowerSet.lower _ (hAR hzA (boundary_le _ _ _ hzY)) hcXY.1
  have hRR : R ⊓ R' = P.boundary R (k + 1) true := by
    refine le_antisymm (fun z ⟨hzR, hzR'⟩ => ?_) (le_inf (boundary_le _ _ _) hYR')
    exact (hVW (hs.isPastingIn.right_le hzR) (hs'.isPastingIn.right_le hzR')).elim
      (fun hzX => LowerSet.lower _ (hAR (boundary_le _ _ _ hzX) hzR) hcXY.2) id
  have hpA : P.IsPastingIn (k + 1) A A' (A ⊔ A') := ⟨rfl, hAA, hAA.trans hA⟩
  have hpR : P.IsPastingIn (k + 1) R R' (R ⊔ R') := ⟨rfl, hRR, hRR.trans hR⟩
  have hinf : (A ⊔ A') ⊓ (R ⊔ R') = A ⊓ R := by
    refine le_antisymm (fun z ⟨hz, hz'⟩ => hs.inf_eq ▸ LowerSet.mem_Iic_iff.2 ?_)
      (inf_le_inf le_sup_left le_sup_left)
    rcases LowerSet.mem_sup_iff.1 hz with hzA | hzA <;>
      rcases LowerSet.mem_sup_iff.1 hz' with hzR | hzR
    · exact hAR hzA hzR
    · exact (hVW (hs.isPastingIn.left_le hzA) (hs'.isPastingIn.right_le hzR)).elim
        (fun hzX => hAR' (hXA' hzX) hzR) fun hzY => hAR hzA (boundary_le _ _ _ hzY)
    · exact (hVW (hs.isPastingIn.right_le hzR) (hs'.isPastingIn.left_le hzA)).elim
        (fun hzX => hAR (boundary_le _ _ _ hzX) hzR) fun hzY => hAR' hzA (hYR' hzY)
    · exact hAR' hzA hzR
  refine ⟨hpA, hpR, ⟨?_, ?_, ?_⟩⟩
  · rw [sup_sup_sup_comm, hs.isPastingIn.sup_eq, hs'.isPastingIn.sup_eq, hp.sup_eq]
  · rw [hinf, hpA.boundary_eq_of_lt_cond false (A := A') (B := A)
      hs'.isMoleculeIn_left.isGlobular hs.isMoleculeIn_left.isGlobular (Nat.succ_pos k) true,
      hs.isPastingIn.inf_eq_output]
  · rw [hinf, hpR.boundary_eq_of_lt_cond false (A := R') (B := R)
      hs'.isMoleculeIn_right.isGlobular hs.isMoleculeIn_right.isGlobular (Nat.succ_pos k) false,
      hs.isPastingIn.inf_eq_input]

private theorem IsTheta.restrict_of_isPastingIn : (k : ℕ) → ∀ {P : OGP.{u}} {V W U : LowerSet P},
    P.IsPastingIn k V W U → IsTheta (P.restrict V) → IsTheta (P.restrict W) →
      IsTheta (P.restrict U)
  | 0 => fun hp hV hW => .restrict_of_isPastingIn_zero hp hV hW
  | k + 1 => by
    rename_i P V W U
    intro hp hV hW
    obtain ⟨⟨ts⟩, ⟨eV⟩⟩ := hV.exists_iso
    clear hV
    induction ts generalizing P V W U with
    | nil =>
      have h0 : krullDim V = 0 := (krullDim_eq_of_iso eV).trans krullDim_theta_node_nil
      rw [hp.eq_right_of_krullDim_le (by rw [h0]; exact_mod_cast Nat.zero_le _)]
      exact hW
    | cons a as iha =>
      rcases le_or_gt (krullDim V) ((k + 1 : ℕ) : WithBot ℕ∞) with hV0 | hV0
      · rw [hp.eq_right_of_krullDim_le hV0]
        exact hW
      rcases le_or_gt (krullDim W) ((k + 1 : ℕ) : WithBot ℕ∞) with hW0 | hW0
      · rw [hp.eq_left_of_krullDim_le hW0]
        exact .iso eV.symm (isTheta_theta _)
      obtain ⟨⟨_ | ⟨b, bs⟩⟩, ⟨eW⟩⟩ := hW.exists_iso
      · refine absurd hW0 (not_lt.2 ?_)
        have h0 : krullDim W = 0 := (krullDim_eq_of_iso eW).trans krullDim_theta_node_nil
        rw [h0]
        exact_mod_cast Nat.zero_le _
      obtain ⟨A, R, v, c, hs, ⟨eA⟩, ⟨eR⟩⟩ := exists_isHeadSplit_of_iso eV.symm
      obtain ⟨A', R', v', c', hs', ⟨eA'⟩, ⟨eR'⟩⟩ := exists_isHeadSplit_of_iso eW.symm
      have hb := hs.boundary (Nat.succ_pos k) true
      have hb' := hs'.boundary (Nat.succ_pos k) false
      rw [← hp.inf_eq_output] at hb
      rw [← hp.inf_eq_input] at hb'
      obtain ⟨hpA, hpR, hp0⟩ := hs.isPastingIn_interchange hp hs' (hb.left_eq_left hb')
        (hb.right_eq_right hb')
      exact .restrict_of_isPastingIn_zero hp0
        (isTheta_restrict_of_isPastingIn_suspension (IsTheta.restrict_of_isPastingIn k) hpA
          (isTheta_theta a) (isTheta_theta b) eA eA')
        (iha hpR (.iso eR'.symm (isTheta_theta _)) eR)

theorem IsTheta.glue {P Q : OGP.{u}} {k : ℕ} (φ : PastingIso P Q k) (hP : IsTheta P)
    (hQ : IsTheta Q) : IsTheta (OGP.glue φ) := by
  obtain ⟨fP⟩ := nonempty_iso_restrict_top P
  obtain ⟨fQ⟩ := nonempty_iso_restrict_top Q
  obtain ⟨f⟩ := nonempty_iso_restrict_top (OGP.glue φ)
  exact .iso f.symm (IsTheta.restrict_of_isPastingIn k (isPastingIn_glue P Q k φ)
    ((restrict_map_iff (fun e h => IsTheta.iso e h) _ _).2 (.iso fP hP))
    ((restrict_map_iff (fun e h => IsTheta.iso e h) _ _).2 (.iso fQ hQ)))

end Paste

private theorem and_isTheta_of_forall_isGlobe {C : OGP.{u} → Prop}
    (iso : ∀ {P Q : OGP.{u}}, (P ≅ Q) → C P → C Q) (globe : ∀ n, C (globe.{u} n))
    (paste : ∀ {P Q : OGP.{u}} (k : ℕ) (φ : PastingIso P Q k), IsTheta P → IsTheta Q → C P →
      C Q → (k : WithBot ℕ∞) < min (krullDim P) (krullDim Q) → C (OGP.glue φ))
    {P : OGP.{u}} (hP : IsGeneratedMolecule P)
    (h : ∀ x : P, IsGlobe (P.restrict (LowerSet.Iic x))) : C P ∧ IsTheta P := by
  induction hP with
  | point => exact ⟨globe 0, .point⟩
  | iso e _ ih =>
    have h' := ih fun x => by
      have hx := (restrict_map_iff (fun e h => IsGlobe.iso e h) e.hom _).1
        (map_Iic e.hom x ▸ h (e.hom x))
      exact hx
    exact ⟨iso e h'.1, .iso e h'.2⟩
  | paste k φ _ _ hk ihP ihQ =>
    have hP := ihP fun p => (restrict_map_iff (fun e h => IsGlobe.iso e h) (glue.inl φ) _).1
      (map_Iic (glue.inl φ) p ▸ h (glue.inl φ p))
    have hQ := ihQ fun q => (restrict_map_iff (fun e h => IsGlobe.iso e h) (glue.inr φ) _).1
      (map_Iic (glue.inr φ) q ▸ h (glue.inr φ q))
    exact ⟨paste k φ hP.2 hQ.2 hP.1 hQ.1 hk, .glue φ hP.2 hQ.2⟩
  | rewrite n φ _ _ hPr hQr hPd hQd _ _ _ =>
    obtain ⟨f⟩ := nonempty_iso_restrict_top (rewrite n φ hPr hQr hPd hQd)
    have hg : IsGlobe ((rewrite n φ hPr hQr hPd hQd).restrict ⊤) := by
      rw [rewrite.top_eq_Iic n φ hPr hQr hPd hQd]
      exact h ⊤
    obtain ⟨m, ⟨e⟩⟩ := hg.iso f.symm
    exact ⟨iso e.symm (globe m), (hg.iso f.symm).isTheta⟩

theorem isTheta_iff_forall_isGlobe {P : OGP.{u}} (hP : P.IsMolecule) :
    IsTheta P ↔ ∀ x : P, IsGlobe (P.restrict (LowerSet.Iic x)) :=
  ⟨IsTheta.isGlobe_Iic, fun h => (and_isTheta_of_forall_isGlobe (C := fun _ => True)
    (fun _ _ => trivial) (fun _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
    ((isGeneratedMolecule_iff_isMolecule P).2 hP) h).2⟩

theorem IsTheta.induction_on_globe_paste {C : OGP.{u} → Prop}
    (iso : ∀ {P Q : OGP.{u}}, (P ≅ Q) → C P → C Q) (globe : ∀ n, C (globe.{u} n))
    (paste : ∀ {P Q : OGP.{u}} (k : ℕ) (φ : PastingIso P Q k), IsTheta P → IsTheta Q → C P →
      C Q → (k : WithBot ℕ∞) < min (krullDim P) (krullDim Q) → C (OGP.glue φ))
    {P : OGP.{u}} (h : IsTheta P) : C P :=
  (and_isTheta_of_forall_isGlobe iso globe paste
    ((isGeneratedMolecule_iff_isMolecule P).2 h.isMolecule) h.isGlobe_Iic).1

private theorem nonempty_dual_suspension_iso (Y : OGP.{u}) (J : ℕ → Bool) :
    Nonempty (dual (suspension Y) J ≅ suspension (dual Y fun n => J (n + 1))) := by
  let f : SuspCarrier Y → SuspCarrier Y := fun w => match w with
    | pole α => pole (xor (J 1) α)
    | susp y => susp y
  have hf (w : SuspCarrier Y) : f (f w) = w := by
    cases w <;> simp [f]
  refine ⟨isoMk (Q := suspension (dual Y fun n => J (n + 1)))
    { toFun := f
      invFun := f
      left_inv := hf
      right_inv := hf
      map_rel_iff' := fun {a b} => ?_ } fun {x y} h => ?_⟩
  · cases a <;> cases b <;> simp [f]
  · rcases x with α | a
    · exact absurd h not_covBy_pole
    rcases y with β | b
    · have ha : grade ℕ a = 0 := grade_eq_zero_iff.2 (pole_covBy_susp.1 h)
      change xor (J 1) β = xor (J (grade ℕ a + 1)) β
      rw [ha]
    · rfl

private theorem isGlobe_dual_globe (n : ℕ) (J : ℕ → Bool) : IsGlobe (dual (globe.{u} n) J) := by
  induction n generalizing J with
  | zero =>
    have hx : IsMin (PUnit.unit : dual point.{u} J) := isMin_point _
    obtain ⟨f⟩ := nonempty_iso_restrict_top (dual point.{u} J)
    exact .iso ((isoPointRestrictIic hx).trans
      ((restrictCongr LowerSet.Iic_top).trans f.symm)) isGlobe_point
  | succ n ih =>
    obtain ⟨e⟩ := nonempty_dual_suspension_iso (globe.{u} n) J
    exact .iso e.symm (ih _).suspension

theorem IsGlobe.dual {P : OGP.{u}} (h : IsGlobe P) (J : ℕ → Bool) : IsGlobe (dual P J) :=
  let ⟨n, ⟨e⟩⟩ := h
  .iso ((dualFunctor J).mapIso e).symm (isGlobe_dual_globe n J)

theorem IsTheta.dual {P : OGP.{u}} (h : IsTheta P) (J : ℕ → Bool) : IsTheta (dual P J) :=
  (isTheta_iff_forall_isGlobe ((isMoleculeIn_dual J).2 h.isMolecule)).2 fun x =>
    .iso (isoMk (OrderIso.refl _) fun _ => rfl) ((h.isGlobe_Iic x).dual J)

end Atoms.Molecule.OGP
