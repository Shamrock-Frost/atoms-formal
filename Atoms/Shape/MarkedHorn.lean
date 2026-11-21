import Atoms.Shape.Horn
import Atoms.Shape.StagedCylinder
import Atoms.Shape.Standard
import Atoms.Molecule.RegularComplex.Morphism

open CategoryTheory Order Set Atoms.Molecule Atoms.Molecule.OGP

namespace Atoms.Shape

theorem Atom.isRewritableSubmolecule_Iic_of_mem_faces (U : Atom) {side : Bool} {face : U.ogp}
    (hface : face ∈ U.ogp.faces side U.top) :
    U.ogp.IsRewritableSubmolecule (.Iic face) (U.ogp.bdry ⊤ side) :=
  hface.2 ▸ (atomicHornDataOfCovBy U face hface.1).rewritable

structure MarkedHornData where
  atom : Atom
  positive : 0 < atom.dimension
  side : Bool
  face : atom.ogp
  face_mem : face ∈ atom.ogp.faces side atom.top
  marking : Set atom.ogp
  marking_mem : ∀ a ∈ marking,
    a ∈ (atom.isRewritableSubmolecule_Iic_of_mem_faces face_mem).hornSet
      atom.isMolecule atom.isAtom.isRound ∧ 0 < grade ℕ a
  left : ℕ → LowerSet atom.ogp
  right : ℕ → LowerSet atom.ogp
  stage : ℕ → LowerSet atom.ogp
  staged : atom.ogp.IsStagedPasting (atom.dimension - 1) (.Iic face) left right stage
  stage_last : stage (atom.dimension - 1) = atom.ogp.bdry ⊤ side
  marked_tops : ∀ i < atom.dimension - 1,
    ∀ y ∈ left (i + 1) ⊔ right (i + 1), grade ℕ y = i + 1 → y ∈ marking

def MarkedHornData.targetMarking (h : MarkedHornData) : Set h.atom.ogp :=
  {a | a = h.atom.top ∨
    (h.atom.ogp.faces (!h.side) h.atom.top ⊆ h.marking ∧ a = h.face) ∨ a ∈ h.marking}

theorem MarkedHornData.mem_targetMarking_iff (h : MarkedHornData) {a : h.atom.ogp} :
    a ∈ h.targetMarking ↔ a = h.atom.top ∨
      (h.atom.ogp.faces (!h.side) h.atom.top ⊆ h.marking ∧ a = h.face) ∨ a ∈ h.marking :=
  Iff.rfl

theorem MarkedHornData.dim_face_add_one (h : MarkedHornData) :
    grade ℕ h.face + 1 = h.atom.dimension := by
  rw [h.atom.dimension_eq, Nat.covBy_iff_add_one_eq.1 (h.face_mem.1.grade ℕ)]

theorem MarkedHornData.dim_face_pos_of_faceSet_subset (h : MarkedHornData)
    (hsub : h.atom.ogp.faces (!h.side) h.atom.top ⊆ h.marking) :
    0 < grade ℕ h.face := by
  have hd := h.dim_face_add_one
  refine Nat.pos_of_ne_zero fun h0 => ?_
  obtain ⟨w, hw⟩ := (h.atom.isMolecule.bdry (h.atom.krullDim_top_pos h.positive) (!h.side)).nonempty
  rw [← h.atom.Iic_top, bdry_Iic] at hw
  obtain ⟨y, hy, -⟩ := mem_lowerClosure.1 hw
  have hyd := Nat.covBy_iff_add_one_eq.1 (hy.1.grade ℕ)
  have hpos := (h.marking_mem y (hsub hy)).2
  rw [← h.atom.dimension_eq] at hyd
  omega

theorem MarkedHornData.targetMarking_mem (h : MarkedHornData) : ∀ a ∈ h.targetMarking,
    a ∈ (⊤ : LowerSet h.atom.ogp) ∧ 0 < grade ℕ a := by
  rintro a (rfl | ⟨hsub, rfl⟩ | hm)
  · exact ⟨LowerSet.mem_top, h.atom.dimension_eq ▸ h.positive⟩
  · exact ⟨LowerSet.mem_top, h.dim_face_pos_of_faceSet_subset hsub⟩
  · exact ⟨LowerSet.mem_top, (h.marking_mem a hm).2⟩

theorem MarkedHornData.isRewritableSubmolecule_closure_face (h : MarkedHornData) :
    h.atom.ogp.IsRewritableSubmolecule (.Iic h.face) (h.atom.ogp.bdry ⊤ h.side) :=
  h.atom.isRewritableSubmolecule_Iic_of_mem_faces h.face_mem

@[simps] def MarkedHornData.toHornData (h : MarkedHornData) : HornData :=
  ⟨h.atom, h.positive, h.side, .Iic h.face, h.isRewritableSubmolecule_closure_face⟩

theorem MarkedHornData.isAtomic (h : MarkedHornData) : h.toHornData.IsAtomic :=
  ⟨h.face, rfl⟩

theorem AtomicHornData.exists_markedHornData (h : AtomicHornData) :
    ∃ m : MarkedHornData, m.toHornData = h.toHornData := by
  obtain ⟨h, x, hx⟩ := h
  have hface := mem_faceSet_top_of_isRewritableSubmolecule h hx
  have hV : h.atom.ogp.IsRewritableSubmolecule (.Iic x)
      (h.atom.ogp.boundary ⊤ (h.atom.dimension - 1) h.side) :=
    hx ▸ h.isRewritableSubmolecule_boundary
  obtain ⟨L, R, M, hs, hMn⟩ := exists_isStagedPasting_of_isSubmoleculeOf hV.isSubmoleculeOf
    (h.atom.dimension - 1) (krullDim_boundary_le _ _ _)
  have hbd : h.atom.ogp.boundary ⊤ (h.atom.dimension - 1) h.side = h.atom.ogp.bdry ⊤ h.side :=
    (h.atom.bdry_top_eq_boundary h.positive h.side).symm
  let hrew := h.atom.isRewritableSubmolecule_Iic_of_mem_faces hface
  let H := hrew.hornSet h.atom.isMolecule h.atom.isAtom.isRound
  let A : Set h.atom.ogp := {a ∈ H | 0 < grade ℕ a}
  have hmarked : ∀ i < h.atom.dimension - 1,
      ∀ y ∈ L (i + 1) ⊔ R (i + 1), grade ℕ y = i + 1 → y ∈ A := by
    intro i hi y hy hyd
    have hyx : y ∉ LowerSet.Iic x := hs.notMem_of_mem_piece hi hy (by omega)
    have hyM : y ∈ M (h.atom.dimension - 1) :=
      hs.stage_le (i + 1) _ hi le_rfl (hs.left_sup_right_le_stage hi hy)
    rw [hMn, hbd] at hyM
    exact ⟨⟨bdry_le_bdryFull ⊤ h.side hyM, fun hyi => hyx hyi.1⟩, by omega⟩
  exact ⟨⟨h.atom, h.positive, h.side, x, hface, A, fun _ ha => ha, L, R, M, hs,
      hMn.trans hbd, hmarked⟩,
    HornData.eq_of_removed_eq _ _ _ hx⟩

namespace MarkedHornData

variable (m : MarkedHornData)

def hornSet : LowerSet m.atom.ogp :=
  hornSubset m.toHornData

abbrev hornRDC : RDCpx.{0} :=
  RDCpx.restrict m.atom.rdc m.hornSet

abbrev hornIncl : m.hornRDC ⟶ m.atom.rdc :=
  RDCpx.restrictIncl m.atom.rdc m.hornSet

theorem bdry_not_subset_hornSet :
    m.atom.ogp.bdry ⊤ (!m.side) ≤ m.hornSet :=
  m.toHornData.bdry_not_subset_hornSubset

theorem mem_hornSet_iff {x : m.atom.ogp} :
    x ∈ m.hornSet ↔ x ∈ m.atom.ogp.bdryFull ⊤ ∧ x ≠ m.face :=
  (mem_hornSet_closure_singleton_iff m.toHornData (x := m.face) (z := x) rfl).trans
    (and_congr_left' (m.atom.mem_bdryFull_top_iff x).symm)

theorem isMoleculeIn_bdry (α : Bool) :
    IsMoleculeIn m.atom.ogp (m.atom.ogp.bdry ⊤ α) :=
  m.atom.isMolecule.bdry (m.atom.krullDim_top_pos m.positive) α

theorem round_bdry (α : Bool) : m.atom.ogp.IsRound (m.atom.ogp.bdry ⊤ α) := by
  rw [m.atom.bdry_top_eq_boundary m.positive]
  exact m.atom.isAtom.isRound.boundary _ α

theorem isMoleculeIn_closure_face :
    IsMoleculeIn m.atom.ogp (.Iic m.face) :=
  m.atom.isRDC m.face

theorem exists_hornSet_eq_singleton (hd : m.atom.dimension = 1) :
    ∃ y, (m.hornSet : Set m.atom.ogp) = {y} := by
  have hside : m.atom.ogp.bdry ⊤ m.side = .Iic m.face := by
    rw [← m.stage_last, ← m.staged.stage_zero, show m.atom.dimension - 1 = 0 by omega]
  have hf0 : IsMin m.face := grade_eq_zero_iff.1 (by have := m.dim_face_add_one; omega)
  have hdS : krullDim (m.atom.ogp.bdry ⊤ (!m.side)) = 0 := by
    rw [m.atom.bdry_top_eq_boundary m.positive, hd, Nat.sub_self,
      m.atom.isMolecule.krullDim_boundary
        (by rw [LowerSet.krullDim_top, m.atom.krullDim_eq_dimension]; exact_mod_cast Nat.zero_le _)]
    rfl
  obtain ⟨y, hy0, hy⟩ := (m.isMoleculeIn_bdry (!m.side)).exists_eq_Iic_of_krullDim_eq_zero hdS
  refine ⟨y, Set.ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · obtain ⟨hzb, hzf⟩ := m.mem_hornSet_iff.1 hz
    have hnot : z ∉ m.atom.ogp.bdry ⊤ m.side := fun hzs =>
      hzf (hf0.eq_of_le (LowerSet.mem_Iic_iff.1 (hside ▸ hzs)))
    rw [bdryFull_eq_bdry_sup_bdry_not ⊤ m.side, LowerSet.mem_sup_iff] at hzb
    have hzb' : z ∈ m.atom.ogp.bdry ⊤ (!m.side) := hzb.resolve_left hnot
    exact hy0.eq_of_le (LowerSet.mem_Iic_iff.1 (hy ▸ hzb'))
  · rw [Set.mem_singleton_iff.1 hz]
    exact m.bdry_not_subset_hornSet (hy.symm ▸ LowerSet.mem_Iic_iff.2 le_rfl)

structure TopPasting (U : Atom) (side : Bool) (face : U.ogp)
    (L N R : LowerSet U.ogp) (marking : Set U.ogp) : Prop where
  left : U.ogp.IsPastingIn (U.dimension - 2) L (.Iic face) N
  right : U.ogp.IsPastingIn (U.dimension - 2) N R (U.ogp.bdry ⊤ side)
  isMoleculeIn_left : IsMoleculeIn U.ogp L
  krullDim_left_le : krullDim L ≤ (U.dimension - 1 : ℕ)
  isMoleculeIn_right : IsMoleculeIn U.ogp R
  krullDim_right_le : krullDim R ≤ (U.dimension - 1 : ℕ)
  marked : ∀ y ∈ L ⊔ R, grade ℕ y = U.dimension - 1 → y ∈ marking

theorem TopPasting.ofCond {U : Atom} (hd : 2 ≤ U.dimension) {side : Bool} {face : U.ogp}
    {P : LowerSet U.ogp} {marking : Set U.ogp} (β : Bool) (hP : IsMoleculeIn U.ogp P)
    (hPd : krullDim P ≤ (U.dimension - 1 : ℕ))
    (hm : ∀ y ∈ P, grade ℕ y = U.dimension - 1 → y ∈ marking)
    (hp : U.ogp.IsPastingIn (U.dimension - 2) (cond β (.Iic face) P) (cond β P (.Iic face))
      (U.ogp.bdry ⊤ side)) :
    TopPasting U side face (cond β (U.ogp.boundary (.Iic face) (U.dimension - 2) (!β)) P)
      (cond β (.Iic face) (U.ogp.bdry ⊤ side))
      (cond β P (U.ogp.boundary (.Iic face) (U.dimension - 2) (!β))) marking := by
  have hI := (U.isRDC face).boundary (U.dimension - 2) (!β)
  have hId : krullDim (U.ogp.boundary (.Iic face) (U.dimension - 2) (!β)) ≤
      (U.dimension - 1 : ℕ) :=
    (krullDim_boundary_le _ _ _).trans (Nat.cast_le.2 (by omega))
  refine ⟨?_, ?_, Bool.cond_rec_prop β hI hP,
    Bool.cond_rec_prop (p := fun X : LowerSet U.ogp => krullDim X ≤ _) β hId hPd,
    Bool.cond_rec_prop β hP hI,
    Bool.cond_rec_prop (p := fun X : LowerSet U.ogp => krullDim X ≤ _) β hPd hId,
    fun y hy hyd => by
      rw [Bool.cond_sup_cond, LowerSet.mem_sup_iff] at hy
      exact hy.elim (fun hy => absurd (grade_le_of_mem_boundary hy) (by omega)) (hm y · hyd)⟩
  all_goals cases β
  · exact hp
  · exact isPastingIn_boundary_false_self _ _
  · have hR := isPastingIn_self_boundary_true (U.ogp.bdry ⊤ side) (U.dimension - 2)
    rwa [hp.boundary_output] at hR
  · exact hp

def ofTopPasting (U : Atom) (hd : 2 ≤ U.dimension) (side : Bool) (face : U.ogp)
    (face_mem : face ∈ U.ogp.faces side U.top) (marking : Set U.ogp)
    (marking_mem : ∀ a ∈ marking,
      a ∈ (U.isRewritableSubmolecule_Iic_of_mem_faces face_mem).hornSet
        U.isMolecule U.isAtom.isRound ∧ 0 < grade ℕ a)
    (L N R : LowerSet U.ogp) (h : TopPasting U side face L N R marking) :
    MarkedHornData where
  atom := U
  positive := by omega
  side := side
  face := face
  face_mem := face_mem
  marking := marking
  marking_mem := marking_mem
  left i := if i = U.dimension - 1 then L else U.ogp.boundary (.Iic face) (i - 1) false
  right i := if i = U.dimension - 1 then R else U.ogp.boundary (.Iic face) (i - 1) true
  stage i := if i = U.dimension - 1 then U.ogp.bdry ⊤ side else .Iic face
  staged := by
    obtain rfl : N = L ⊔ .Iic face := h.left.sup_eq.symm
    have hk : U.dimension - 1 = U.dimension - 2 + 1 := by omega
    have h' := (isStagedPasting_self (U.isRDC face) (U.dimension - 2)).extend h.left h.right
      h.isMoleculeIn_left (hk ▸ h.krullDim_left_le) h.isMoleculeIn_right (hk ▸ h.krullDim_right_le)
    rwa [← hk] at h'
  stage_last := if_pos rfl
  marked_tops i hi y hy hyd := by
    by_cases hlt : i + 1 = U.dimension - 1
    · simp only [if_pos hlt] at hy
      exact h.marked y hy (by omega)
    · simp only [if_neg hlt] at hy
      rcases hy with hy | hy <;> have := grade_le_of_mem_boundary hy <;> omega

def ofStaged (U : Atom) (hpos : 0 < U.dimension) (side : Bool) (face : U.ogp)
    (face_mem : face ∈ U.ogp.faces side U.top) (T : U.ogp → Prop)
    (hT : ∀ a, T a → 0 < grade ℕ a) (L R M : ℕ → LowerSet U.ogp)
    (staged : U.ogp.IsStagedPasting (U.dimension - 1) (.Iic face) L R M)
    (stage_last : M (U.dimension - 1) = U.ogp.bdry ⊤ side)
    (tops : ∀ i < U.dimension - 1, ∀ y ∈ L (i + 1) ⊔ R (i + 1), grade ℕ y = i + 1 → T y) :
    MarkedHornData where
  atom := U
  positive := hpos
  side := side
  face := face
  face_mem := face_mem
  marking := {a ∈ (U.isRewritableSubmolecule_Iic_of_mem_faces face_mem).hornSet
    U.isMolecule U.isAtom.isRound | T a}
  marking_mem a ha := ⟨ha.1, hT a ha.2⟩
  left := L
  right := R
  stage := M
  staged := staged
  stage_last := stage_last
  marked_tops i hi y hy hyd :=
    ⟨⟨bdry_le_bdryFull ⊤ side (stage_last ▸ staged.stage_le (i + 1) _ hi le_rfl
        (staged.left_sup_right_le_stage hi hy)),
      fun h => staged.notMem_of_mem_piece hi hy (by omega) h.1⟩,
      tops i hi y hy hyd⟩

theorem face_notMem_left_union_right {i : ℕ} (hi : i < m.atom.dimension - 1) :
    m.face ∉ m.left (i + 1) ⊔ m.right (i + 1) := fun h =>
  m.staged.notMem_of_mem_piece hi h (by have := m.dim_face_add_one; omega)
    (LowerSet.mem_Iic_iff.2 le_rfl)

theorem left_union_right_subset_hornSet {i : ℕ} (hi : i < m.atom.dimension - 1) :
    m.left (i + 1) ⊔ m.right (i + 1) ≤ m.hornSet :=
  fun _ hx => m.mem_hornSet_iff.2 ⟨bdry_le_bdryFull ⊤ m.side
    (((m.staged.stage_le (i + 1) _ hi le_rfl).trans m.stage_last.le)
      (m.staged.left_sup_right_le_stage hi hx)),
    fun h => m.face_notMem_left_union_right hi (h ▸ hx)⟩

theorem closure_face_subset_bdry :
    LowerSet.Iic m.face ≤ m.atom.ogp.bdry ⊤ m.side :=
  m.stage_last ▸ (m.staged.isSubmoleculeOf_stage (m.atom.isRDC m.face) _ le_rfl).le

theorem boundary_closure_face_subset_hornSet {n : ℕ} (hn : n < grade ℕ m.face)
    (β : Bool) : m.atom.ogp.boundary (.Iic m.face) n β ≤ m.hornSet := fun _ hx =>
  m.mem_hornSet_iff.2 ⟨bdry_le_bdryFull ⊤ m.side (m.closure_face_subset_bdry
    (boundary_le (.Iic m.face) n β hx)),
    fun h => by
      have := grade_le_of_mem_boundary hx
      rw [h] at this
      omega⟩

abbrev faceAtom : Atom := Atom.ofClosure m.atom m.face

def faceEmb : m.faceAtom.ogp ⟶ m.atom.ogp :=
  Atom.closureInclOGP m.atom m.face

instance : IsInclusion m.faceEmb :=
  inferInstanceAs (IsInclusion (Atom.closureInclOGP m.atom m.face))

theorem image_faceEmb : map m.faceEmb ⊤ = .Iic m.face :=
  Atom.map_closureInclOGP_top m.atom m.face

theorem dimension_faceAtom_add_one : m.faceAtom.dimension + 1 = m.atom.dimension :=
  (congrArg (· + 1) (Atom.dimension_ofClosure m.atom m.face)).trans m.dim_face_add_one

theorem faceEmb_mem_closure (y : m.faceAtom.ogp) :
    m.faceEmb y ∈ LowerSet.Iic m.face :=
  closureIncl_mem_closure m.atom m.face y

theorem faceEmb_mem_bdryFull (y : m.faceAtom.ogp) :
    m.faceEmb y ∈ m.atom.ogp.bdryFull ⊤ :=
  bdry_le_bdryFull ⊤ m.side (m.closure_face_subset_bdry (m.faceEmb_mem_closure y))

theorem faceEmb_mem_hornSet {y : m.faceAtom.ogp}
    (hy : y ∈ m.faceAtom.ogp.bdryFull ⊤) :
    m.faceEmb y ∈ m.hornSet := by
  have hy' : m.faceEmb y ∈ map m.faceEmb (m.faceAtom.ogp.bdryFull ⊤) := ⟨y, hy, rfl⟩
  rw [map_bdryFull, m.image_faceEmb] at hy'
  exact m.isRewritableSubmolecule_closure_face.isSubmoleculeOf.bdryFull_le_hornSet
    m.atom.isMolecule m.atom.isAtom.isRound m.isRewritableSubmolecule_closure_face.krullDim_eq hy'

def faceSphere : m.faceAtom.ogp.restrict (m.faceAtom.ogp.bdryFull ⊤) ⟶
    m.atom.ogp.restrict m.hornSet :=
  codRestrict (incl (m.faceAtom.ogp.bdryFull ⊤) ≫ m.faceEmb) m.hornSet
    fun y => m.faceEmb_mem_hornSet y.2

instance : IsInclusion m.faceSphere :=
  ⟨fun _ _ hxy => IsInclusion.injective (f := incl (m.faceAtom.ogp.bdryFull ⊤) ≫ m.faceEmb)
    (congrArg (incl m.hornSet) hxy)⟩

theorem hornSet_subset_bdryFull :
    m.hornSet ≤ m.atom.ogp.bdryFull ⊤ :=
  fun _ hx => hx.1

def hornToSphere : m.atom.ogp.restrict m.hornSet ⟶
    m.atom.ogp.restrict (m.atom.ogp.bdryFull ⊤) :=
  codRestrict (incl m.hornSet) (m.atom.ogp.bdryFull ⊤)
    fun x => m.hornSet_subset_bdryFull x.2

instance : IsInclusion m.hornToSphere :=
  inferInstanceAs (IsInclusion (codRestrict (incl m.hornSet) (m.atom.ogp.bdryFull ⊤)
    fun x => m.hornSet_subset_bdryFull x.2))

def faceToSphere : m.faceAtom.ogp ⟶ m.atom.ogp.restrict (m.atom.ogp.bdryFull ⊤) :=
  codRestrict m.faceEmb (m.atom.ogp.bdryFull ⊤) m.faceEmb_mem_bdryFull

instance : IsInclusion m.faceToSphere :=
  inferInstanceAs (IsInclusion (codRestrict m.faceEmb (m.atom.ogp.bdryFull ⊤)
    m.faceEmb_mem_bdryFull))

theorem hornToSphere_cover :
    map m.hornToSphere ⊤ ⊔ map m.faceToSphere ⊤ = ⊤ := by
  refine top_unique fun x _ => ?_
  by_cases hx : x.1 = m.face
  · have hmem : x.1 ∈ map m.faceEmb ⊤ := by
      rw [m.image_faceEmb, hx]
      exact LowerSet.mem_Iic_iff.2 le_rfl
    obtain ⟨y, -, hy⟩ := hmem
    exact Or.inr ⟨y, LowerSet.mem_top, Subtype.ext hy⟩
  · exact Or.inl ⟨⟨x.1, m.mem_hornSet_iff.2 ⟨x.2, hx⟩⟩, LowerSet.mem_top, rfl⟩

theorem image_faceSphere_comp :
    map (m.faceSphere ≫ m.hornToSphere) ⊤ =
      map m.hornToSphere ⊤ ⊓ map m.faceToSphere ⊤ := by
  refine SetLike.ext fun x => ⟨?_, ?_⟩
  · rintro ⟨y, -, rfl⟩
    exact ⟨⟨m.faceSphere y, LowerSet.mem_top, rfl⟩, ⟨y.1, LowerSet.mem_top, rfl⟩⟩
  · rintro ⟨⟨z, -, hz⟩, ⟨y, -, rfl⟩⟩
    have e : z.1 = m.faceEmb y := congrArg Subtype.val hz
    have hz' : m.faceEmb y ∈ m.hornSet := e ▸ z.2
    have hb : m.faceEmb y ∈ m.atom.ogp.bdryFull (.Iic m.face) :=
      (m.isRewritableSubmolecule_closure_face.isSubmoleculeOf.mem_hornSet_iff_of_mem
        m.atom.isMolecule m.atom.isAtom.isRound
        m.isRewritableSubmolecule_closure_face.krullDim_eq (m.faceEmb_mem_closure y)).1 hz'
    rw [← m.image_faceEmb, ← map_bdryFull] at hb
    obtain ⟨y', hy', he⟩ := hb
    exact ⟨⟨y, IsInclusion.injective (f := m.faceEmb) he ▸ hy'⟩, LowerSet.mem_top, rfl⟩

end MarkedHornData

section Compositor

variable (U : RoundShape) (hU : 0 < U.dimension)

def compositorFace : (toMergerAtom U hU).ogp :=
  U.outputIncl (Nat.sub_add_cancel hU).symm (mergerAtom U hU).top

theorem closure_compositorFace :
    LowerSet.Iic (compositorFace U hU) = (toMergerAtom U hU).ogp.bdry ⊤ true := by
  have h := map_Iic (U.outputIncl (Nat.sub_add_cancel hU).symm) (mergerAtom U hU).top
  have htop : LowerSet.Iic (mergerAtom U hU).top = (⊤ : LowerSet (U.merger _).ogp) :=
    (mergerAtom U hU).Iic_top
  exact h.symm.trans ((congrArg (map _) htop).trans (U.map_outputIncl _))

theorem compositorFace_mem_faceSet :
    compositorFace U hU ∈ (toMergerAtom U hU).ogp.faces true (toMergerAtom U hU).top := by
  have hb : compositorFace U hU ∈
      (toMergerAtom U hU).ogp.bdry (.Iic (toMergerAtom U hU).top) true := by
    rw [(toMergerAtom U hU).Iic_top, ← closure_compositorFace]
    exact LowerSet.mem_Iic_iff.2 le_rfl
  refine mem_faces_of_mem_bdry_Iic hb ?_
  have hg : grade ℕ (compositorFace U hU) = grade ℕ (mergerAtom U hU).top :=
    (isMorphism (U.outputIncl (Nat.sub_add_cancel hU).symm)).grade_eq (mergerAtom U hU).top
  rw [hg, ← (mergerAtom U hU).dimension_eq, dimension_mergerAtom,
    ← (toMergerAtom U hU).dimension_eq, dimension_toMergerAtom]

def compositorMarkedHorn : MarkedHornData :=
  MarkedHornData.ofTopPasting (toMergerAtom U hU) (by rw [dimension_toMergerAtom]; omega) true
    (compositorFace U hU) (compositorFace_mem_faceSet U hU) ∅
    (fun a ha => absurd ha (Set.notMem_empty a)) _ _ _
    (.ofCond (by rw [dimension_toMergerAtom]; omega) true
      (((toMergerAtom U hU).isRDC (compositorFace U hU)).boundary
        ((toMergerAtom U hU).dimension - 2) true)
      ((krullDim_boundary_le _ _ _).trans (Nat.cast_le.2 (by omega)))
      (fun _ hy hyd => absurd (grade_le_of_mem_boundary hy) (by
        rw [hyd, dimension_toMergerAtom]
        omega))
      (by
        rw [← closure_compositorFace]
        exact isPastingIn_self_boundary_true _ _))

theorem hornSet_compositorFace :
    (compositorMarkedHorn U hU).hornSet = map (toMergerInputIncl U hU) ⊤ := by
  have hB : (toMergerAtom U hU).ogp.IsSubmoleculeOf
      ((toMergerAtom U hU).ogp.bdry ⊤ (!false)) ((toMergerAtom U hU).ogp.bdry ⊤ (!false)) :=
    .refl ((compositorMarkedHorn U hU).isMoleculeIn_bdry (!false))
  have heq : (compositorMarkedHorn U hU).hornSet =
      hB.hornSet (toMergerAtom U hU).isMolecule (toMergerAtom U hU).isAtom.isRound rfl :=
    SetLike.coe_injective (congrArg (((toMergerAtom U hU).ogp.bdryFull ⊤ : Set _) \
      (toMergerAtom U hU).ogp.interior ·) (closure_compositorFace U hU))
  exact heq.trans ((hB.hornSet_bdry (toMergerAtom U hU).isMolecule
    (toMergerAtom U hU).isAtom.isRound
    ((toMergerAtom U hU).krullDim_top_of_pos (pos_dimension_toMergerAtom U hU)) rfl).trans
    (U.map_inputIncl (Nat.sub_add_cancel hU).symm).symm)

def compositorHornIso :
    U.ogp ≅ (toMergerAtom U hU).ogp.restrict (compositorMarkedHorn U hU).hornSet :=
  isoRestrictOfFintype (toMergerInputIncl U hU) (hornSet_compositorFace U hU).symm

theorem inputEmb_mem_horn (x : U.ogp) :
    toMergerInputIncl U hU x ∈ (compositorMarkedHorn U hU).hornSet := by
  rw [hornSet_compositorFace]
  exact ⟨x, LowerSet.mem_top, rfl⟩

instance : @IsInclusion U.rdc.obj.toOGP (compositorMarkedHorn U hU).hornRDC.obj.toOGP
    (codRestrict (toMergerInputIncl U hU)
      (compositorMarkedHorn U hU).hornSet (inputEmb_mem_horn U hU)) :=
  ⟨fun _ _ hxy => IsInclusion.injective (f := toMergerInputIncl U hU)
    (congrArg (incl (compositorMarkedHorn U hU).hornSet) hxy)⟩

theorem inputEmb_comp_compositorHornIso :
    RDCpx.ofInclusion (P := U.rdc) (Q := (compositorMarkedHorn U hU).hornRDC)
      (codRestrict (toMergerInputIncl U hU)
        (compositorMarkedHorn U hU).hornSet (inputEmb_mem_horn U hU)) ≫
      (RDCpx.isoOfIso (compositorHornIso U hU).symm).hom = 𝟙 U.rdc := by
  ext x
  exact ConcreteCategory.congr_hom (compositorHornIso U hU).hom_inv_id x

def compositorTopMarkedHorn : MarkedHornData :=
  MarkedHornData.ofTopPasting (toMergerAtom U hU) (by rw [dimension_toMergerAtom]; omega) true
    (compositorFace U hU) (compositorFace_mem_faceSet U hU)
    {a | a ∈ (compositorMarkedHorn U hU).hornSet ∧ grade ℕ a = U.dimension}
    (fun _ ha => ⟨ha.1, ha.2 ▸ hU⟩) _ _ _
    (.ofCond (by rw [dimension_toMergerAtom]; omega) true
      (((toMergerAtom U hU).isRDC (compositorFace U hU)).boundary
        ((toMergerAtom U hU).dimension - 2) true)
      ((krullDim_boundary_le _ _ _).trans (Nat.cast_le.2 (by omega)))
      (fun _ hy hyd => absurd (grade_le_of_mem_boundary hy) (by
        rw [hyd, dimension_toMergerAtom]
        omega))
      (by
        rw [← closure_compositorFace]
        exact isPastingIn_self_boundary_true _ _))

theorem faces_compositorTopMarkedHorn_subset_marking :
    (compositorTopMarkedHorn U hU).atom.ogp.faces (!(compositorTopMarkedHorn U hU).side)
      (compositorTopMarkedHorn U hU).atom.top ⊆ (compositorTopMarkedHorn U hU).marking := by
  intro b hb
  have hf := (compositorTopMarkedHorn U hU).face_mem
  refine ⟨(compositorTopMarkedHorn U hU).mem_hornSet_iff.2
    ⟨((compositorTopMarkedHorn U hU).atom.mem_bdryFull_top_iff b).2 hb.1.lt.ne, fun hbf => ?_⟩, ?_⟩
  · rw [← hbf] at hf
    exact Bool.not_ne_self _ (hb.2.symm.trans hf.2)
  · have hg := Nat.covBy_iff_add_one_eq.1 (hb.1.grade ℕ)
    have ht := (toMergerAtom U hU).dimension_eq
    have hd := dimension_toMergerAtom U hU
    change grade ℕ b + 1 = grade ℕ (toMergerAtom U hU).top at hg
    exact Nat.succ.inj (hg.trans (ht.symm.trans hd))

end Compositor

theorem bdry_grayCylinder_obj (U : Atom) (β : Bool) :
    (grayCylinder.obj U).ogp.bdry ⊤ β =
      map (cylAtomIso U).hom (OGP.copyWhisker β ⊤ U.dimension) := by
  have hU : krullDim (⊤ : LowerSet U.ogp) ≤ (U.dimension : ℕ) := by
    rw [LowerSet.krullDim_top, U.krullDim_eq_dimension]
  have hpos : 0 < (grayCylinder.obj U).dimension := by
    rw [dimension_grayCylinder_obj]; exact Nat.succ_pos _
  have hd : (grayCylinder.obj U).dimension - 1 = U.dimension := by
    rw [dimension_grayCylinder_obj]; omega
  rw [(grayCylinder.obj U).bdry_top_eq_boundary hpos, hd, ← map_top_of_isIso (cylAtomIso U).hom,
    ← map_boundary, ← LowerSet.top_prod_top]
  exact congrArg (map (cylAtomIso U).hom) (OGP.boundary_arrowProd_univ_top U.isMolecule hU β)

private theorem exists_isStagedPasting_map_cylAtomIso (U : Atom) {k : ℕ}
    {X S : LowerSet (OGP.arrowCyl U.ogp)} {T : OGP.arrowCyl U.ogp → Prop}
    (h : ∃ L R M : ℕ → LowerSet (OGP.arrowCyl U.ogp),
      (OGP.arrowCyl U.ogp).IsStagedPasting k X L R M ∧ M k = S ∧ OGP.StagedTops k L R T) :
    ∃ L R M : ℕ → LowerSet (grayCylinder.obj U).ogp,
      (grayCylinder.obj U).ogp.IsStagedPasting k (map (cylAtomIso U).hom X) L R M ∧
      M k = map (cylAtomIso U).hom S ∧
      ∀ i < k, ∀ y ∈ L (i + 1) ⊔ R (i + 1), grade ℕ y = i + 1 → T ((cylAtomIso U).inv y) := by
  obtain ⟨L, R, M, hs, hM, ht⟩ := h
  refine ⟨fun i => map (cylAtomIso U).hom (L i), fun i => map (cylAtomIso U).hom (R i),
    fun i => map (cylAtomIso U).hom (M i), hs.map (cylAtomIso U).hom, congrArg _ hM,
    fun i hi y hy hyd => ?_⟩
  rw [← OGP.map_sup] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [Iso.hom_inv_id_apply]
  exact ht i hi z hz (((isMorphism (cylAtomIso U).hom).grade_eq z).symm.trans hyd)

theorem exists_isStagedPasting_endpoint (U : Atom) (β : Bool) :
    ∃ L R M : ℕ → LowerSet (grayCylinder.obj U).ogp,
      (grayCylinder.obj U).ogp.IsStagedPasting ((grayCylinder.obj U).dimension - 1)
        (.Iic ((cylAtomIso U).hom (SuspCarrier.pole β, U.top))) L R M ∧
      M ((grayCylinder.obj U).dimension - 1) = (grayCylinder.obj U).ogp.bdry ⊤ β ∧
      ∀ i < (grayCylinder.obj U).dimension - 1, ∀ y ∈ L (i + 1) ⊔ R (i + 1),
        grade ℕ y = i + 1 →
          ((cylAtomIso U).inv y).1 = ⊤ := by
  have hd : (grayCylinder.obj U).dimension - 1 = U.dimension := by
    rw [dimension_grayCylinder_obj]; omega
  rw [hd, Iic_cylAtomIso, U.Iic_top, bdry_grayCylinder_obj]
  exact exists_isStagedPasting_map_cylAtomIso U
    (OGP.exists_isStagedPasting_copyWhisker U.isMolecule β (n := U.dimension) le_rfl)

theorem MarkedHornData.exists_isStagedPasting_cylinder (m : MarkedHornData) :
    ∃ L R M : ℕ → LowerSet (grayCylinder.obj m.atom).ogp,
      (grayCylinder.obj m.atom).ogp.IsStagedPasting ((grayCylinder.obj m.atom).dimension - 1)
        (.Iic ((cylAtomIso m.atom).hom (⊤, m.face))) L R M ∧
      M ((grayCylinder.obj m.atom).dimension - 1) =
        (grayCylinder.obj m.atom).ogp.bdry ⊤ (!m.side) ∧
      ∀ i < (grayCylinder.obj m.atom).dimension - 1, ∀ y ∈ L (i + 1) ⊔ R (i + 1),
        grade ℕ y = i + 1 →
          ((cylAtomIso m.atom).inv y).1 = ⊤ ∨
            ((cylAtomIso m.atom).inv y).2 ∈ m.targetMarking := by
  have hpos := m.positive
  have hU := m.atom.toMoleculeShape.krullDim_top_eq (Nat.sub_add_cancel hpos).symm
  have hd : (grayCylinder.obj m.atom).dimension - 1 = m.atom.dimension - 1 + 1 := by
    rw [dimension_grayCylinder_obj]; omega
  have hM : m.stage (m.atom.dimension - 1) =
      m.atom.ogp.boundary ⊤ (m.atom.dimension - 1) m.side := by
    rw [m.stage_last, m.atom.bdry_top_eq_boundary hpos]
  obtain ⟨L, R, M, hs, hM', ht⟩ := OGP.exists_isStagedPasting_arrowProd_top m.atom.isMolecule
    m.isMoleculeIn_closure_face hU m.side m.staged hM
  rw [hd, Iic_cylAtomIso, LowerSet.Iic_top, bdry_grayCylinder_obj]
  refine exists_isStagedPasting_map_cylAtomIso m.atom
    (T := fun z => z.1 = ⊤ ∨ z.2 ∈ m.targetMarking)
    ⟨L, R, M, hs, hM'.trans (by rw [Nat.sub_add_cancel hpos]), fun i hi z hz hgz => ?_⟩
  rcases ht i hi z hz hgz with (h | ⟨j, hj, hzj, hzd⟩) | ⟨-, -, hzd⟩
  · exact Or.inl h
  · exact Or.inr (m.mem_targetMarking_iff.2 (Or.inr (Or.inr (m.marked_tops j hj _ hzj hzd))))
  · exact Or.inr (m.mem_targetMarking_iff.2 (Or.inl (GradeOrder.eq_of_le_of_grade_le
      (m.atom.le_top _) (by rw [← m.atom.dimension_eq]; omega))))

end Atoms.Shape
