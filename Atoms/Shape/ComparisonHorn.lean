import Atoms.Shape.MarkedHorn
import Atoms.Molecule.Cylinder.StagedOver
import Atoms.Molecule.Cylinder.Unitor

open CategoryTheory Order Set Atoms.Molecule Atoms.Molecule.OGP Atoms.Molecule.OGP.PartialCylinder

namespace Atoms.Shape.MarkedHornData

variable (m : MarkedHornData)

instance decidableMemHornSet : DecidablePred (· ∈ m.hornSet) := fun x =>
  decidable_of_iff (x ≠ m.atom.top ∧ x ≠ m.face)
    (m.mem_hornSet_iff.trans (and_congr_left' (m.atom.mem_bdryFull_top_iff x))).symm

theorem top_notMem_hornSet : m.atom.top ∉ m.hornSet := fun h =>
  (m.mem_hornSet_iff.1 h).1 |> (m.atom.mem_bdryFull_top_iff _).1 |>.elim rfl

theorem face_notMem_hornSet : m.face ∉ m.hornSet := fun h => (m.mem_hornSet_iff.1 h).2 rfl

private theorem mem_hornSet_of_grade_lt {y : m.atom.ogp} (hy : y ∈ m.atom.ogp.bdry ⊤ m.side)
    (hd : grade ℕ y + 1 < m.atom.dimension) : y ∈ m.hornSet :=
  m.mem_hornSet_iff.2 ⟨bdry_le_bdryFull ⊤ m.side hy, fun h => by
    have := m.dim_face_add_one
    rw [h] at hd
    omega⟩

def comparisonLeft (i : ℕ) : LowerSet (partialCylinder m.atom.ogp m.hornSet) :=
  if i = m.atom.dimension then
    cond m.side (copy m.hornSet false ⊤)
      ((partialCylinder m.atom.ogp m.hornSet).boundary
        (over m.hornSet (m.stage (m.atom.dimension - 1))) (m.atom.dimension - 1) false)
  else over m.hornSet (m.left i)

def comparisonStage (i : ℕ) : LowerSet (partialCylinder m.atom.ogp m.hornSet) :=
  if i = m.atom.dimension then
    (partialCylinder m.atom.ogp m.hornSet).boundary ⊤ m.atom.dimension (!m.side)
  else over m.hornSet (m.stage i)

def comparisonRight (i : ℕ) : LowerSet (partialCylinder m.atom.ogp m.hornSet) :=
  if i = m.atom.dimension then
    cond m.side ((partialCylinder m.atom.ogp m.hornSet).boundary
        ((partialCylinder m.atom.ogp m.hornSet).boundary ⊤ m.atom.dimension (!m.side))
        (m.atom.dimension - 1) true)
      (copy m.hornSet true ⊤)
  else over m.hornSet (m.right i)

theorem isStagedPasting_comparisonStage (hd : 2 ≤ m.atom.dimension) :
    (partialCylinder m.atom.ogp m.hornSet).IsStagedPasting m.atom.dimension
      (over m.hornSet (.Iic m.face)) m.comparisonLeft m.comparisonRight m.comparisonStage := by
  set d := m.atom.dimension with hd_def
  set K := m.hornSet
  have hU := m.atom.isMolecule
  have hdim : krullDim m.atom.ogp = d := m.atom.krullDim_eq_dimension
  have hlast : m.stage (d - 1) = m.atom.ogp.boundary ⊤ (d - 1) m.side := by
    rw [m.stage_last, bdry_eq_boundary (n := d - 1)
      (by rw [LowerSet.krullDim_top, hdim]; exact_mod_cast (Nat.sub_add_cancel (by omega)).symm)]
  have h1 := m.staged.over (K := K)
    (fun i hi => le_sup_left.trans (m.left_union_right_subset_hornSet hi))
    (fun i hi => le_sup_right.trans (m.left_union_right_subset_hornSet hi))
    (fun i hi y hy hyd => m.mem_hornSet_of_grade_lt
      (m.stage_last ▸ m.staged.stage_le (i + 1) _ hi le_rfl hy) (by omega))
  rw [← hd_def] at h1
  have hsub : m.atom.ogp.boundary ⊤ (d - 2) (!(!m.side)) ≤ K := fun y hy => by
    rw [Bool.not_not] at hy
    refine m.mem_hornSet_iff.2 ⟨?_, fun h => ?_⟩
    · exact (m.atom.mem_bdryFull_top_iff y).2 fun ht => by
        have := grade_le_of_mem_boundary hy
        rw [ht, ← m.atom.dimension_eq] at this
        omega
    · have := grade_le_of_mem_boundary hy
      have := m.dim_face_add_one
      rw [h] at *
      omega
  have hP := isPastingIn_endSet_succ hU (endStatement_of_subset hU hsub)
  rw [endSet_eq_copy hsub, show d - 2 + 1 = d - 1 by omega] at hP
  have hN : endSet K (!m.side) (d - 1) =
      (partialCylinder m.atom.ogp K).boundary ⊤ d (!m.side) :=
    (boundary_partialCylinder_dimension K hU hdim (by omega) (!m.side)).symm
  rw [hN, Bool.not_not, ← hlast] at hP
  have hMm : IsMoleculeIn _ (over K (m.stage (d - 1))) := h1.isMoleculeIn_stage _ le_rfl
  have hC : IsMoleculeIn _ (copy K (!m.side) ⊤) := isMoleculeIn_copy hU _
  have hdC : krullDim (copy K (!m.side) ⊤) ≤ ((d - 1 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [krullDim_copy, LowerSet.krullDim_top, hdim, Nat.sub_add_cancel (by omega)]
  have e : d - 1 + 1 = d := by omega
  cases hs : m.side
  · rw [hs] at hP hC hdC
    simp only [Bool.not_false, cond_true] at hP hC hdC
    have h2 := h1.extend
      (l := (partialCylinder m.atom.ogp K).boundary (over K (m.stage (d - 1))) (d - 1) false)
      (by rw [sup_eq_right.2 (boundary_le _ _ _)]; exact isPastingIn_boundary_false_self _ _)
      (by rw [sup_eq_right.2 (boundary_le _ _ _)]; exact hP) (hMm.boundary _ _)
      ((krullDim_boundary_le _ _ _).trans (by exact_mod_cast Nat.le_succ _)) hC hdC
    rw [e] at h2
    convert h2 using 3 <;>
      simp only [comparisonLeft, comparisonRight, comparisonStage, hs, cond_false,
        Bool.not_false] <;> rfl
  · rw [hs] at hP hC hdC
    simp only [Bool.not_true, cond_false] at hP hC hdC
    have hP' : (partialCylinder m.atom.ogp K).IsPastingIn (d - 1) (copy K false ⊤)
        (over K (m.stage (d - 1))) (copy K false ⊤ ⊔ over K (m.stage (d - 1))) := by
      rw [hP.sup_eq]; exact hP
    have h2 := h1.extend hP' (isPastingIn_self_boundary_true _ (d - 1)) hC hdC
      ((hP'.isMoleculeIn hC hMm).boundary _ _)
      ((krullDim_boundary_le _ _ _).trans (by exact_mod_cast Nat.le_succ _))
    rw [hP.sup_eq, e] at h2
    convert h2 using 3 <;>
      simp only [comparisonLeft, comparisonRight, comparisonStage, hs, cond_true,
        Bool.not_true] <;> rfl

private theorem eq_mkI_top_of_mem_copy {β : Bool} {y : partialCylinder m.atom.ogp m.hornSet}
    (hy : y ∈ copy m.hornSet β ⊤) (hd : grade ℕ y = m.atom.dimension) :
    y = mkI m.hornSet (some β) m.atom.top m.top_notMem_hornSet := by
  have hlt (x : m.atom.ogp) (hx : x ∈ m.hornSet) : grade ℕ x < m.atom.dimension := by
    rw [m.atom.dimension_eq]
    exact grade_strictMono (lt_of_le_of_ne (m.atom.le_top x) fun h => m.top_notMem_hornSet (h ▸ hx))
  rcases y with ⟨x, hx⟩ | ⟨⟨_ | γ⟩, ⟨x, hx⟩⟩
  · exact absurd hd (grade_mkK (K := m.hornSet) hx ▸ (hlt x hx).ne)
  · exact (mkI_none_notMem_copy hx hy).elim
  · obtain ⟨rfl, -⟩ := (mkI_some_mem_copy hx).1 hy
    have hg : grade ℕ x = m.atom.dimension := (grade_mkI_some (K := m.hornSet) γ hx).symm.trans hd
    obtain rfl : x = m.atom.top :=
      GradeOrder.eq_of_le_of_grade_le (m.atom.le_top x) (by rw [← m.atom.dimension_eq, hg])
    rfl

theorem comparison_tops (hd : 2 ≤ m.atom.dimension) {i : ℕ} (hi : i < m.atom.dimension)
    {y : partialCylinder m.atom.ogp m.hornSet}
    (hy : y ∈ m.comparisonLeft (i + 1) ⊔ m.comparisonRight (i + 1)) (hyd : grade ℕ y = i + 1) :
    partialCylinderProj _ _ y ∈ m.marking ∨
      y = mkI m.hornSet (some (!m.side)) m.atom.top m.top_notMem_hornSet := by
  by_cases h : i + 1 = m.atom.dimension
  · have hb (A : LowerSet (partialCylinder m.atom.ogp m.hornSet)) (β : Bool)
        (hA : y ∈ (partialCylinder m.atom.ogp m.hornSet).boundary A (m.atom.dimension - 1) β) :
        False := by
      have := grade_le_of_mem_boundary hA
      omega
    simp only [comparisonLeft, comparisonRight, if_pos h] at hy
    cases hs : m.side <;> rw [hs] at hy <;>
      simp only [cond_true, cond_false, Bool.not_true, Bool.not_false] at hy <;>
      rcases hy with hy | hy
    · exact (hb _ _ hy).elim
    · exact Or.inr (m.eq_mkI_top_of_mem_copy hy (hyd.trans h))
    · exact Or.inr (m.eq_mkI_top_of_mem_copy hy (hyd.trans h))
    · exact (hb _ _ hy).elim
  · have hi' : i < m.atom.dimension - 1 := by omega
    simp only [comparisonLeft, comparisonRight, if_neg h, ← over_sup] at hy
    have hK := m.left_union_right_subset_hornSet hi' hy
    refine Or.inl (m.marked_tops i hi' _ hy ?_)
    rw [eq_mkK_of_proj_mem hK, grade_mkK] at hyd
    exact hyd

private theorem Iic_mkI_none {x : m.atom.ogp} (hx : x ∉ m.hornSet) :
    LowerSet.Iic (mkI m.hornSet none x hx) = over m.hornSet (.Iic x) :=
  SetLike.ext fun _ => ⟨fun h => proj_le_proj (LowerSet.mem_Iic_iff.1 h),
    fun h => LowerSet.mem_Iic_iff.2 (le_mkI_none_of_proj_le hx h)⟩

theorem isAtom_partialCylinder_hornSet : IsAtom (partialCylinder m.atom.ogp m.hornSet) := by
  refine ⟨isMolecule_partialCylinder m.atom.isMolecule _, mkI _ none m.atom.top
    m.top_notMem_hornSet, ?_⟩
  rw [Iic_mkI_none, m.atom.Iic_top, over_top]

@[implicit_reducible] def comparisonAtom : Atom :=
  Atom.ofIsAtom (cylShape m.atom.toMoleculeShape m.hornSet).toFiniteOGP
    ((isAtom_iff_of_iso (cylShapeIso m.atom.toMoleculeShape m.hornSet)).1
      m.isAtom_partialCylinder_hornSet)

def comparisonIso : partialCylinder m.atom.ogp m.hornSet ≅ m.comparisonAtom.ogp :=
  cylShapeIso m.atom.toMoleculeShape m.hornSet

theorem comparisonAtom_top :
    m.comparisonAtom.top = m.comparisonIso.hom (mkI _ none m.atom.top m.top_notMem_hornSet) := by
  refine le_antisymm ?_ (m.comparisonAtom.le_top _)
  rw [← Iso.inv_hom_id_apply m.comparisonIso m.comparisonAtom.top]
  exact (isMorphism m.comparisonIso.hom).monotone
    (le_mkI_none_of_proj_le m.top_notMem_hornSet (m.atom.le_top _))

theorem dimension_comparisonAtom : m.comparisonAtom.dimension = m.atom.dimension + 1 := by
  rw [m.comparisonAtom.dimension_eq, comparisonAtom_top, (isMorphism m.comparisonIso.hom).grade_eq,
    grade_mkI_none, m.atom.dimension_eq]

def comparisonFace : m.comparisonAtom.ogp :=
  m.comparisonIso.hom (mkI _ none m.face m.face_notMem_hornSet)

theorem comparisonFace_mem :
    m.comparisonFace ∈ m.comparisonAtom.ogp.faces (!m.side) m.comparisonAtom.top := by
  obtain ⟨hc, ho⟩ := m.face_mem
  rw [comparisonAtom_top, comparisonFace, IsInclusion.mem_faces_iff]
  refine ⟨(covBy_mkI_none_mkI_none _ _).2 hc, ?_⟩
  rw [orient_mkI_none_mkI_none _ _ hc, ho]

def comparisonMarkedHorn (hd : 2 ≤ m.atom.dimension) : MarkedHornData :=
  ofStaged m.comparisonAtom (by rw [dimension_comparisonAtom]; omega) (!m.side) m.comparisonFace
    m.comparisonFace_mem
    (fun a => partialCylinderProj _ _ (m.comparisonIso.inv a) ∈ m.marking ∨
      ∃ β, m.comparisonIso.inv a = mkI _ (some β) m.atom.top m.top_notMem_hornSet)
    (fun a ha => by
      rw [← (isMorphism m.comparisonIso.inv).grade_eq]
      rcases ha with ha | ⟨β, hβ⟩
      · exact ((m.marking_mem _ ha).2).trans_le (grade_proj_le _)
      · rw [hβ, grade_mkI_some, ← m.atom.dimension_eq]
        omega)
    (fun i => OGP.map m.comparisonIso.hom (m.comparisonLeft i))
    (fun i => OGP.map m.comparisonIso.hom (m.comparisonRight i))
    (fun i => OGP.map m.comparisonIso.hom (m.comparisonStage i))
    (by
      rw [dimension_comparisonAtom, Nat.add_sub_cancel, comparisonFace, ← map_Iic, Iic_mkI_none]
      exact (m.isStagedPasting_comparisonStage hd).map m.comparisonIso.hom)
    (by
      rw [dimension_comparisonAtom, Nat.add_sub_cancel, comparisonStage, if_pos rfl,
        map_boundary, map_top_of_isIso, bdry_eq_boundary (by
          rw [LowerSet.krullDim_top, m.comparisonAtom.krullDim_eq_dimension,
            dimension_comparisonAtom]; rfl)])
    (fun i hi y hy hyd => by
      rw [dimension_comparisonAtom, Nat.add_sub_cancel] at hi
      rw [← OGP.map_sup] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      rw [Iso.hom_inv_id_apply]
      rw [(isMorphism m.comparisonIso.hom).grade_eq] at hyd
      exact (m.comparison_tops hd hi hy' hyd).imp_right fun h => ⟨_, h⟩)

@[simp] theorem comparisonMarkedHorn_atom (hd : 2 ≤ m.atom.dimension) :
    (m.comparisonMarkedHorn hd).atom = m.comparisonAtom := rfl

@[simp] theorem comparisonMarkedHorn_side (hd : 2 ≤ m.atom.dimension) :
    (m.comparisonMarkedHorn hd).side = !m.side := rfl

private theorem exists_eq_of_mem_faces_comparisonAtom_top {b : m.comparisonAtom.ogp}
    (hb : b ∈ m.comparisonAtom.ogp.faces m.side m.comparisonAtom.top) :
    ∃ β, m.comparisonIso.inv b = mkI _ (some β) m.atom.top m.top_notMem_hornSet := by
  rw [← Iso.inv_hom_id_apply m.comparisonIso b, comparisonAtom_top,
    IsInclusion.mem_faces_iff] at hb
  obtain ⟨hc, ho⟩ := hb
  generalize m.comparisonIso.inv b = c at hc ho ⊢
  rcases c with ⟨y, hy⟩ | ⟨⟨_ | β⟩, ⟨y, hy⟩⟩
  · exact (not_covBy_mkK_mkI_none hy _ hc).elim
  · have hyc := (covBy_mkI_none_mkI_none hy _).1 hc
    rw [orient_mkI_none_mkI_none _ _ hyc] at ho
    have hyf : y ∈ m.atom.ogp.faces (!m.side) m.atom.top := ⟨hyc, by rw [← ho, Bool.not_not]⟩
    refine (hy (m.mem_hornSet_iff.2 ⟨(m.atom.mem_bdryFull_top_iff y).2 hyc.lt.ne, ?_⟩)).elim
    rintro rfl
    exact Bool.not_ne_self m.side (hyf.2.symm.trans m.face_mem.2)
  · obtain rfl := (covBy_mkI_some_mkI_none β hy _).1 hc
    exact ⟨β, rfl⟩

theorem faces_comparisonMarkedHorn_subset_marking (hd : 2 ≤ m.atom.dimension) :
    (m.comparisonMarkedHorn hd).atom.ogp.faces (!(m.comparisonMarkedHorn hd).side)
      (m.comparisonMarkedHorn hd).atom.top ⊆ (m.comparisonMarkedHorn hd).marking := by
  rw [comparisonMarkedHorn_side, Bool.not_not]
  intro b hb
  refine ⟨(m.comparisonMarkedHorn hd).mem_hornSet_iff.2
    ⟨((m.comparisonMarkedHorn hd).atom.mem_bdryFull_top_iff b).2 hb.1.lt.ne, fun hbf => ?_⟩,
    Or.inr (m.exists_eq_of_mem_faces_comparisonAtom_top hb)⟩
  have hf := (m.comparisonMarkedHorn hd).face_mem
  rw [← hbf, comparisonMarkedHorn_side] at hf
  exact Bool.not_ne_self m.side (hf.2.symm.trans hb.2)

theorem cylEndpoint_mem_comparisonHornSet (hd : 2 ≤ m.atom.dimension) (β : Bool)
    (v : m.atom.ogp) :
    cylEndpoint m.atom.toMoleculeShape m.hornSet β v ∈ (m.comparisonMarkedHorn hd).hornSet := by
  refine (m.comparisonMarkedHorn hd).mem_hornSet_iff.2
    ⟨(m.comparisonAtom.mem_bdryFull_top_iff _).2 fun h => ?_, fun h => ?_⟩
  · rw [comparisonAtom_top] at h
    exact endpoint_ne_mkI_none m.hornSet β v m.atom.top m.top_notMem_hornSet
      (IsInclusion.injective (f := m.comparisonIso.hom) h)
  · exact endpoint_ne_mkI_none m.hornSet β v m.face m.face_notMem_hornSet
      (IsInclusion.injective (f := m.comparisonIso.hom) h)

def comparisonHornEndpoint (hd : 2 ≤ m.atom.dimension) (β : Bool) :
    m.atom.ogp ⟶
      (m.comparisonMarkedHorn hd).atom.ogp.restrict (m.comparisonMarkedHorn hd).hornSet :=
  codRestrict (cylEndpoint m.atom.toMoleculeShape m.hornSet β) _
    (m.cylEndpoint_mem_comparisonHornSet hd β)

instance (hd : 2 ≤ m.atom.dimension) (β : Bool) : IsInclusion (m.comparisonHornEndpoint hd β) :=
  ⟨fun _ _ h => IsInclusion.injective (f := cylEndpoint m.atom.toMoleculeShape m.hornSet β)
    (congrArg Subtype.val h)⟩

theorem comparisonHornEndpoint_cover (hd : 2 ≤ m.atom.dimension) :
    map (m.comparisonHornEndpoint hd false) ⊤ ⊔ map (m.comparisonHornEndpoint hd true) ⊤ = ⊤ := by
  refine top_unique fun y _ => ?_
  have hc : m.comparisonIso.hom (m.comparisonIso.inv y.1) = y.1 := Iso.inv_hom_id_apply _ _
  generalize m.comparisonIso.inv y.1 = c at hc
  rcases eq_endpoint_or_eq_mkI_none c with ⟨β, v, rfl⟩ | ⟨v, hv, rfl⟩
  · cases β
    · exact Or.inl ⟨v, LowerSet.mem_top, Subtype.ext hc⟩
    · exact Or.inr ⟨v, LowerSet.mem_top, Subtype.ext hc⟩
  · have hy := (m.comparisonMarkedHorn hd).mem_hornSet_iff.1 y.2
    by_cases hvt : v = m.atom.top
    · subst hvt
      exact ((m.comparisonAtom.mem_bdryFull_top_iff _).1 hy.1
        (hc.symm.trans m.comparisonAtom_top.symm)).elim
    · obtain rfl : v = m.face := by
        by_contra hvf
        exact hv (m.mem_hornSet_iff.2 ⟨(m.atom.mem_bdryFull_top_iff v).2 hvt, hvf⟩)
      exact (hy.2 hc.symm).elim

theorem comparisonHornEndpoint_incl (hd : 2 ≤ m.atom.dimension)
    (y : m.atom.ogp.restrict m.hornSet) :
    m.comparisonHornEndpoint hd false (incl m.hornSet y) =
      m.comparisonHornEndpoint hd true (incl m.hornSet y) :=
  Subtype.ext (congrArg m.comparisonIso.hom
    ((endpoint_of_mem false y.2).trans (endpoint_of_mem true y.2).symm))

theorem map_incl_comp_comparisonHornEndpoint (hd : 2 ≤ m.atom.dimension) :
    map (incl m.hornSet ≫ m.comparisonHornEndpoint hd false) ⊤ =
      map (m.comparisonHornEndpoint hd false) ⊤ ⊓ map (m.comparisonHornEndpoint hd true) ⊤ := by
  refine SetLike.ext fun y => ⟨?_, ?_⟩
  · rintro ⟨v, -, rfl⟩
    exact ⟨⟨_, LowerSet.mem_top, rfl⟩,
      ⟨_, LowerSet.mem_top, (m.comparisonHornEndpoint_incl hd v).symm⟩⟩
  · rintro ⟨⟨v, -, rfl⟩, ⟨v', -, hv'⟩⟩
    have h : partialCylinderEndpoint _ m.hornSet true v' =
        partialCylinderEndpoint _ m.hornSet false v :=
      IsInclusion.injective (f := m.comparisonIso.hom) (congrArg Subtype.val hv')
    have hv : v ∈ m.hornSet := by
      by_contra hv
      rw [endpoint_of_notMem false hv] at h
      by_cases hv'K : v' ∈ m.hornSet
      · rw [endpoint_of_mem true hv'K] at h
        exact mkK_ne_mkI hv'K hv h
      · rw [endpoint_of_notMem true hv'K, mkI_eq_mkI_iff] at h
        exact absurd h.1 (by decide)
    exact ⟨⟨v, hv⟩, LowerSet.mem_top, rfl⟩

theorem boundary_Iic_comparisonFace (hd : 2 ≤ m.atom.dimension) (β : Bool) :
    m.comparisonAtom.ogp.boundary (.Iic m.comparisonFace) (grade ℕ m.face) β =
      map (cylEndpoint m.atom.toMoleculeShape m.hornSet β) (.Iic m.face) := by
  have hg := (m.atom.isRDC m.face).isGlobular
  have hf := m.dim_face_add_one
  obtain ⟨e, he⟩ : ∃ e, grade ℕ m.face = e + 1 := ⟨grade ℕ m.face - 1, by omega⟩
  have hsub : m.atom.ogp.boundary (.Iic m.face) e (!β) ≤ m.hornSet := fun y hy => by
    have hy' := grade_le_of_mem_boundary hy
    refine m.mem_hornSet_iff.2 ⟨(m.atom.mem_bdryFull_top_iff y).2 fun h => ?_, fun h => ?_⟩
    · rw [h, ← m.atom.dimension_eq] at hy'
      omega
    · rw [h] at hy'
      omega
  rw [comparisonFace, ← map_Iic, m.Iic_mkI_none m.face_notMem_hornSet, ← map_boundary,
    Molecule.cylEndpoint, map_comp, map_partialCylinderEndpoint, he, boundary_over_succ hg,
    boundary_eq_self (by rw [LowerSet.krullDim_Iic, he]) β, over_eq_copy_of_le hsub β,
    sup_eq_left.2 (copy_mono β (boundary_le _ _ _))]
  rfl

end Atoms.Shape.MarkedHornData
