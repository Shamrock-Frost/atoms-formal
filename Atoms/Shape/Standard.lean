import Atoms.Shape.Collapse
import Atoms.Shape.Rigidity
import Atoms.Molecule.MoleculeShape.Merger
import Atoms.Molecule.Construction.SimplexFull
import Atoms.Molecule.MoleculeShape.AtomBoundaryIso
import Atoms.Molecule.MoleculeShape.PartialCylinder
import Atoms.Molecule.Vertex

open CategoryTheory Limits Order Simplicial Atoms.Molecule Atoms.Molecule.OGP

namespace Atoms.Shape

def atomPoint : Atom := Atom.ofOGP point isAtom_point

def atomGlobe (n : ℕ) : Atom := Atom.ofOGP (globe n) (isAtom_globe n)

theorem dimension_atomGlobe (n : ℕ) : (atomGlobe n).dimension = n := by
  have h := (atomGlobe n).krullDim_eq_dimension.symm.trans
    ((krullDim_eq_of_orderIso (orderIsoOfIso (FiniteOGP.ofOGPIso (globe n)))).symm.trans
      (krullDim_globe n))
  exact_mod_cast h

def atomGlobeVertex (ε : Bool) : atomPoint ⟶ atomGlobe 1 :=
  letI := IsInclusion.comp (suspension.poleIncl (globe.{0} 0) ε) (FiniteOGP.ofOGPIso (globe 1)).hom
  letI hf := IsInclusion.comp (FiniteOGP.ofOGPIso point).inv
    (suspension.poleIncl (globe.{0} 0) ε ≫ (FiniteOGP.ofOGPIso (globe 1)).hom)
  @Atom.ofInclusion atomPoint (atomGlobe 1) _ hf

theorem atomGlobeVertex_apply (ε : Bool) (x : atomPoint.ogp) :
    atomGlobeVertex ε x = (FiniteOGP.ofOGPIso (globe 1)).hom (SuspCarrier.pole ε) := by
  change (FiniteOGP.ofOGPIso (globe 1)).hom
    (suspension.poleIncl (globe.{0} 0) ε ((FiniteOGP.ofOGPIso point).inv x)) = _
  rw [suspension.poleIncl_apply]

instance uniqueAtomPointCarrier : Unique atomPoint.ogp :=
  letI : Unique point := inferInstanceAs (Unique PUnit)
  (orderIsoOfIso (FiniteOGP.ofOGPIso point)).toEquiv.symm.unique

theorem dimension_atomPoint : atomPoint.dimension = 0 :=
  dimension_atomGlobe 0

def toAtomPoint (U : Atom) : U ⟶ atomPoint :=
  haveI := functor_isFibered_constPoint (P := U.ogp)
  Atom.conjHom (Iso.refl U.ogp) (FiniteOGP.ofOGPIso point) (fun _ => (⊤ : point))
    (isMap_constPoint U.isRDC)

instance (U : Atom) : Subsingleton (U ⟶ atomPoint) :=
  ⟨fun _ _ => Atom.hom_ext fun _ => Subsingleton.elim _ _⟩

theorem isCollapseHom_toAtomPoint (U : Atom) : IsCollapseHom (toAtomPoint U) :=
  fun _ => ⟨U.top, Subsingleton.elim _ _⟩

theorem isIso_toAtomPoint_of_dimension_eq_zero {U : Atom} (h : U.dimension = 0) :
    IsIso (toAtomPoint U) :=
  isIso_of_isCollapseHom_of_dimension_eq _ (isCollapseHom_toAtomPoint U)
    (by rw [h, dimension_atomPoint])

theorem exists_point_apply_top {U : Atom} {v : U.ogp} (hv : grade ℕ v = 0) :
    ∃ x : atomPoint ⟶ U, x atomPoint.top = v := by
  have := isIso_toAtomPoint_of_dimension_eq_zero (U := Atom.ofClosure U v)
    (by rw [Atom.dimension_ofClosure, hv])
  exact ⟨inv (toAtomPoint (Atom.ofClosure U v)) ≫ Atom.closureIncl U v,
    (congrArg (Atom.closureIncl U v)
      (isCollapseHom_of_iso (asIso (toAtomPoint (Atom.ofClosure U v))).symm).apply_top).trans
        (Atom.closureIncl_top U v)⟩

theorem boundary_atomGlobe_one (α : Bool) :
    (atomGlobe 1).ogp.boundary (.Iic (atomGlobe 1).top) 0 α =
      .Iic (atomGlobeVertex α atomPoint.top) := by
  have h := congrArg (map (FiniteOGP.ofOGPIso (globe 1)).hom) (boundary_zero_globe_one α)
  rw [map_boundary, map_top_of_isIso, map_Iic, ← atomGlobeVertex_apply α atomPoint.top] at h
  rw [Atom.Iic_top]
  exact h

def isTerminalAtomPoint : IsTerminal atomPoint :=
  IsTerminal.ofUniqueHom toAtomPoint fun _ _ => Subsingleton.elim _ _

instance hasTerminal_atom : HasTerminal Atom := isTerminalAtomPoint.hasTerminal

theorem exists_inclusion_atomPoint (U : Atom) : ∃ f : atomPoint ⟶ U, IsInclusionHom f := by
  obtain ⟨x, hx, -⟩ := (U.isAtom.1.boundary 0 false).exists_eq_Iic_of_krullDim_eq_zero
    (U.isAtom.1.krullDim_boundary
      (by rw [LowerSet.krullDim_top, U.krullDim_eq_dimension]; exact_mod_cast Nat.zero_le _) false)
  have := isIso_toAtomPoint_of_dimension_eq_zero (U := Atom.ofClosure U x)
    (by rw [Atom.dimension_ofClosure, grade_eq_zero_iff.2 hx])
  refine ⟨inv (toAtomPoint (Atom.ofClosure U x)) ≫ Atom.closureIncl U x, ?_⟩
  exact (Atom.isInclusionHom_closureIncl U x).comp
    (isInclusionHom_of_mono (inv (toAtomPoint (Atom.ofClosure U x))))

def atomSimplex (n : ℕ) : Atom := Atom.ofOGP (simplex n) (isAtom_simplex n)

def atomSimplexZeroIsoPoint : atomSimplex 0 ≅ atomPoint :=
  Iso.refl _

def simplexHom {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) : atomSimplex m ⟶ atomSimplex n :=
  haveI := functor_isFibered_simplexMap f
  Atom.conjHom (FiniteOGP.ofOGPIso (simplex m)) (FiniteOGP.ofOGPIso (simplex n)) (simplexMap f)
    (isMap_simplexMap f)

theorem simplexHom_apply {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (x : (atomSimplex m).ogp) :
    simplexHom f x = (FiniteOGP.ofOGPIso (simplex n)).hom
      (simplexMap f ((FiniteOGP.ofOGPIso (simplex m)).inv x)) :=
  rfl

theorem simplexHom_id (m : ℕ) :
    simplexHom (OrderHom.id : Fin (m + 1) →o Fin (m + 1)) = 𝟙 (atomSimplex m) := by
  ext x
  rw [simplexHom_apply, simplexMap_id]
  exact Iso.inv_hom_id_apply _ x

theorem simplexHom_comp {m n k : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (n + 1) →o Fin (k + 1)) : simplexHom (g.comp f) = simplexHom f ≫ simplexHom g := by
  ext x
  rw [ConcreteCategory.comp_apply, simplexHom_apply, simplexHom_apply, simplexHom_apply,
    simplexMap_comp, Iso.hom_inv_id_apply]

theorem isInclusionHom_simplexHom_of_injective {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (hf : Function.Injective f) : IsInclusionHom (simplexHom f) :=
  haveI := functor_isFibered_simplexMap f
  Atom.isInclusionHom_conjHom _ _ _ (injective_simplexMap_of_injective f hf)

theorem isCollapseHom_simplexHom_of_surjective {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (hf : Function.Surjective f) : IsCollapseHom (simplexHom f) :=
  haveI := functor_isFibered_simplexMap f
  Atom.isCollapseHom_conjHom _ _ _ (surjective_simplexMap_of_surjective f hf)

def atomSimplexOneIsoGlobe : atomSimplex 1 ≅ atomGlobe 1 :=
  Atom.isoOfOGPIso ((FiniteOGP.ofOGPIso (simplex 1)).symm ≪≫ simplexOneIsoGlobeOne ≪≫
    FiniteOGP.ofOGPIso (globe 1))

theorem simplexHom_δ_comp_atomSimplexOneIsoGlobe_hom (ε : Bool) :
    simplexHom (SimplexCategory.δ (cond ε 0 1 : Fin 2)).toOrderHom ≫ atomSimplexOneIsoGlobe.hom =
      atomGlobeVertex ε := by
  refine Atom.hom_ext fun x => ?_
  change (FiniteOGP.ofOGPIso (globe 1)).hom (simplexOneIsoGlobeOne.hom
    ((FiniteOGP.ofOGPIso (simplex 1)).inv ((FiniteOGP.ofOGPIso (simplex 1)).hom
      (simplexMap _ ((FiniteOGP.ofOGPIso (simplex 0)).inv x))))) = _
  rw [Iso.hom_inv_id_apply, simplexOneIsoGlobeOne_simplexMap_δ]
  exact (atomGlobeVertex_apply ε x).symm

def atomSimplexVertices (s : ℕ) (x : (atomSimplex s).ogp) : Finset (Fin (s + 1)) :=
  simplexVertices s ((FiniteOGP.ofOGPIso (simplex s)).inv x)

theorem atomSimplexVertices_subset_iff {s : ℕ} {x y : (atomSimplex s).ogp} :
    atomSimplexVertices s x ⊆ atomSimplexVertices s y ↔ x ≤ y :=
  (simplexVertices_subset_iff s).trans
    (orderIsoOfIso (FiniteOGP.ofOGPIso (simplex s)).symm).le_iff_le

theorem card_atomSimplexVertices {s : ℕ} (x : (atomSimplex s).ogp) :
    (atomSimplexVertices s x).card = grade ℕ x + 1 := by
  rw [atomSimplexVertices, card_simplexVertices]
  exact congrArg (· + 1) ((isMorphism (FiniteOGP.ofOGPIso (simplex s)).inv).grade_eq x)

theorem atomSimplexVertices_injective (s : ℕ) : Function.Injective (atomSimplexVertices s) :=
  fun _ _ h => le_antisymm (atomSimplexVertices_subset_iff.1 h.subset)
    (atomSimplexVertices_subset_iff.1 h.superset)

theorem exists_atomSimplexVertices_eq (s : ℕ) {S : Finset (Fin (s + 1))} (hS : S.Nonempty) :
    ∃ x, atomSimplexVertices s x = S := by
  obtain ⟨x, hx⟩ := exists_simplexVertices_eq s S hS
  exact ⟨(FiniteOGP.ofOGPIso (simplex s)).hom x, (congrArg (simplexVertices s)
    (ConcreteCategory.congr_hom (FiniteOGP.ofOGPIso (simplex s)).hom_inv_id x)).trans hx⟩

theorem atomSimplexVertices_simplexHom {m s : ℕ} (σ : Fin (m + 1) →o Fin (s + 1))
    (x : (atomSimplex m).ogp) :
    atomSimplexVertices s (simplexHom σ x) = (atomSimplexVertices m x).image σ :=
  (congrArg (simplexVertices s) (Iso.hom_inv_id_apply _ _)).trans (simplexVertices_simplexMap σ _)

theorem hom_ext_atomSimplex {U : Atom} {s : ℕ} {f g : U ⟶ atomSimplex s}
    (h : ∀ v, grade ℕ v = 0 → f v = g v) : f = g := by
  have key : ∀ f g : U ⟶ atomSimplex s, (∀ v, grade ℕ v = 0 → f v = g v) →
      ∀ x, atomSimplexVertices s (f x) ⊆ atomSimplexVertices s (g x) := by
    intro f g h x j hj
    obtain ⟨w, hw⟩ := exists_atomSimplexVertices_eq s (Finset.singleton_nonempty j)
    have hw0 : grade ℕ w = 0 := by
      have := card_atomSimplexVertices w
      rw [hw, Finset.card_singleton] at this
      omega
    have hwx : w ≤ f x :=
      atomSimplexVertices_subset_iff.1 (hw ▸ Finset.singleton_subset_iff.2 hj)
    obtain ⟨x', hx'x, hx'w⟩ := (Atom.isMap f).fibration hwx
    obtain ⟨v, hvx', hfv, hv0⟩ := (Atom.isMap f).exists_le_apply_eq x'
    rw [hx'w, hw0] at hv0
    have := atomSimplexVertices_subset_iff.2 ((Atom.isMap g).monotone (hvx'.trans hx'x))
    rw [← h v hv0, hfv, hx'w, hw] at this
    exact Finset.singleton_subset_iff.1 this
  exact Atom.hom_ext fun x => atomSimplexVertices_injective s
    (Finset.Subset.antisymm (key f g h x) (key g f (fun v hv => (h v hv).symm) x))

theorem exists_comp_simplexHom_eq_iff {U : Atom} {m n : ℕ} {e : Fin (m + 1) →o Fin (n + 1)}
    (he : Function.Injective e) (f : U ⟶ atomSimplex n) :
    (∃ g, g ≫ simplexHom e = f) ↔
      atomSimplexVertices n (f U.top) ⊆ Finset.univ.image e := by
  refine ⟨?_, fun h => exists_comp_eq_of_isInclusionHom _
    (isInclusionHom_simplexHom_of_injective e he) f fun t => ?_⟩
  · rintro ⟨g, rfl⟩
    rw [ConcreteCategory.comp_apply, atomSimplexVertices_simplexHom]
    exact Finset.image_subset_image (Finset.subset_univ _)
  · set S := atomSimplexVertices n (f t)
    have ht : S ⊆ Finset.univ.image e :=
      (atomSimplexVertices_subset_iff.2 ((Atom.isMap f).monotone (U.le_top t))).trans h
    have himg : (S.preimage e he.injOn).image e = S := by
      rw [Finset.image_preimage, Finset.filter_true_of_mem]
      exact fun j hj => (Finset.mem_image.1 (ht hj)).imp fun _ => And.right
    have hne : (S.preimage e he.injOn).Nonempty := by
      rw [← Finset.image_nonempty (f := e), himg]
      exact simplexVertices_nonempty n _
    obtain ⟨a, ha⟩ := exists_atomSimplexVertices_eq m hne
    exact ⟨a, atomSimplexVertices_injective n (by rw [atomSimplexVertices_simplexHom, ha, himg])⟩

theorem orient_atomSimplex_erase {n : ℕ} {x y : (atomSimplex n).ogp} {v : Fin (n + 1)}
    (hv : v ∈ atomSimplexVertices n x)
    (hy : atomSimplexVertices n y = (atomSimplexVertices n x).erase v) (hyx : y ⋖ x) :
    (atomSimplex n).ogp.orient hyx =
      decide (((atomSimplexVertices n x).filter fun w => w < v).card % 2 = 0) :=
  ((isMorphism (FiniteOGP.ofOGPIso (simplex n)).inv).orient_apply hyx).symm.trans
    (orient_simplex_erase n hv hy _)

theorem boundary_closure_zero_atomSimplex {n : ℕ} (y : (atomSimplex n).ogp) (α : Bool)
    {w : (atomSimplex n).ogp} {j : Fin (n + 1)} (hw : atomSimplexVertices n w = {j})
    (hj : j ∈ atomSimplexVertices n y)
    (hext : ∀ i ∈ atomSimplexVertices n y, i ≠ j → (i < j ↔ α = true)) :
    (atomSimplex n).ogp.boundary (LowerSet.Iic y) 0 α = LowerSet.Iic w := by
  have hwy : w ≤ y := atomSimplexVertices_subset_iff.1 (hw ▸ Finset.singleton_subset_iff.2 hj)
  have hw0 : grade ℕ w = 0 := by
    have := card_atomSimplexVertices w
    rw [hw, Finset.card_singleton] at this
    omega
  rw [boundary_zero_eq_Iic_iff ((atomSimplex n).isRDC y)
    (LowerSet.mem_Iic_iff.2 hwy) hw0]
  intro e he hwe
  have he1 : (atomSimplexVertices n e).card = 2 := by
    rw [card_atomSimplexVertices, ← Nat.covBy_iff_add_one_eq.1 (hwe.grade ℕ), hw0]
  have hje : j ∈ atomSimplexVertices n e :=
    atomSimplexVertices_subset_iff.2 hwe.le (hw ▸ Finset.mem_singleton_self j)
  obtain ⟨a, b, hab, hE⟩ := Finset.card_eq_two.1 he1
  obtain ⟨i, hij, hEi⟩ : ∃ i, i ≠ j ∧ atomSimplexVertices n e = {i, j} := by
    rw [hE] at hje ⊢
    rcases Finset.mem_insert.1 hje with rfl | h
    · exact ⟨b, hab.symm, Finset.pair_comm _ _⟩
    · rw [Finset.mem_singleton] at h
      subst h
      exact ⟨a, hab, rfl⟩
  have hiy : i ∈ atomSimplexVertices n y :=
    atomSimplexVertices_subset_iff.2 (LowerSet.mem_Iic_iff.1 he)
      (hEi ▸ Finset.mem_insert_self i {j})
  have hy' : atomSimplexVertices n w = (atomSimplexVertices n e).erase i := by
    rw [hw, hEi, Finset.erase_insert (by simpa using hij)]
  rw [orient_atomSimplex_erase (hEi ▸ Finset.mem_insert_self i {j}) hy' hwe, hEi,
    Finset.filter_insert, if_neg (lt_irrefl i), Finset.filter_singleton]
  have := hext i hiy hij
  cases α
  · have hji : j < i := lt_of_le_of_ne (not_lt.1 fun h => absurd (this.1 h) (by simp))
      (Ne.symm hij)
    simp [hji]
  · have hij' := this.2 rfl
    simp [not_lt.2 hij'.le]

theorem le_of_mem_boundary_zero_true_atomSimplex {s : ℕ} {x v : (atomSimplex s).ogp}
    (hv : v ∈ (atomSimplex s).ogp.boundary (.Iic x) 0 true)
    {j j' : Fin (s + 1)} (hj : atomSimplexVertices s v = {j})
    (hj' : j' ∈ atomSimplexVertices s x) : j' ≤ j := by
  set m := (atomSimplexVertices s x).max' ⟨j', hj'⟩
  obtain ⟨w, hw⟩ := exists_atomSimplexVertices_eq s (Finset.singleton_nonempty m)
  rw [boundary_closure_zero_atomSimplex x true hw (Finset.max'_mem _ _) fun i hi hne =>
    iff_of_true (lt_of_le_of_ne (Finset.le_max' _ i hi) hne) rfl] at hv
  have h := atomSimplexVertices_subset_iff.2 (LowerSet.mem_Iic_iff.1 hv)
  rw [hj, hw, Finset.singleton_subset_singleton] at h
  rw [h]
  exact Finset.le_max' _ j' hj'

def simplexFunctor : SimplexCategory ⥤ Atom where
  obj n := atomSimplex n.len
  map f := simplexHom f.toOrderHom
  map_id n := by
    rw [SimplexCategory.id_toOrderHom]
    exact simplexHom_id n.len
  map_comp f g := by
    rw [SimplexCategory.comp_toOrderHom]
    exact simplexHom_comp f.toOrderHom g.toOrderHom

theorem simplexFunctor_obj (n : SimplexCategory) : simplexFunctor.obj n = atomSimplex n.len :=
  rfl

theorem simplexFunctor_map {m n : SimplexCategory} (f : m ⟶ n) :
    simplexFunctor.map f = simplexHom f.toOrderHom :=
  rfl

instance faithful_simplexFunctor : simplexFunctor.Faithful where
  map_injective {m n} f f' h := by
    refine SimplexCategory.Hom.ext f f' (simplexMap_injective (funext fun x => ?_))
    have key : ∀ g : m ⟶ n, (FiniteOGP.ofOGPIso (simplex n.len)).inv
        (simplexFunctor.map g ((FiniteOGP.ofOGPIso (simplex m.len)).hom x)) =
          simplexMap g.toOrderHom x := fun g =>
      (congrArg (fun y => (FiniteOGP.ofOGPIso (simplex n.len)).inv
          ((FiniteOGP.ofOGPIso (simplex n.len)).hom (simplexMap g.toOrderHom y)))
        (ConcreteCategory.congr_hom (FiniteOGP.ofOGPIso (simplex m.len)).hom_inv_id x)).trans
        (ConcreteCategory.congr_hom (FiniteOGP.ofOGPIso (simplex n.len)).hom_inv_id _)
    exact (key f).symm.trans
      ((congrArg (fun φ : simplexFunctor.obj m ⟶ simplexFunctor.obj n =>
        (FiniteOGP.ofOGPIso (simplex n.len)).inv
          (φ ((FiniteOGP.ofOGPIso (simplex m.len)).hom x))) h).trans (key f'))

instance full_simplexFunctor : simplexFunctor.Full where
  map_surjective {m n} φ := by
    obtain ⟨f, hf⟩ := exists_simplexMap_eq_of_isMap
      (((isMap_of_isInclusion (FiniteOGP.ofOGPIso (simplex m.len)).hom).comp
        (Atom.isMap φ)).comp (isMap_of_isInclusion (FiniteOGP.ofOGPIso (simplex n.len)).inv))
    refine ⟨SimplexCategory.mkHom f, Atom.hom_ext fun x => ?_⟩
    have hx := congrFun hf ((FiniteOGP.ofOGPIso (simplex m.len)).inv x)
    exact (congrArg (FiniteOGP.ofOGPIso (simplex n.len)).hom hx.symm).trans
      ((Iso.inv_hom_id_apply _ _).trans (congrArg φ (Iso.inv_hom_id_apply _ x)))

def mergerAtom (U : RoundShape) (hU : 0 < U.dimension) : Atom :=
  Atom.ofIsAtom (U.merger (Nat.sub_add_cancel hU).symm).toFiniteOGP
    (U.isAtom_merger (Nat.sub_add_cancel hU).symm)

def toMergerAtom (U : RoundShape) (hU : 0 < U.dimension) : Atom :=
  Atom.ofIsAtom (U.toMerger (Nat.sub_add_cancel hU).symm).toFiniteOGP
    (U.isAtom_toMerger (Nat.sub_add_cancel hU).symm)

def toMergerInputIncl (U : RoundShape) (hU : 0 < U.dimension) : U.ogp ⟶ (toMergerAtom U hU).ogp :=
  U.inputIncl (Nat.sub_add_cancel hU).symm

instance (U : RoundShape) (hU : 0 < U.dimension) : IsInclusion (toMergerInputIncl U hU) :=
  inferInstanceAs (IsInclusion (U.inputIncl (Nat.sub_add_cancel hU).symm))

theorem dimension_toMergerAtom (U : RoundShape) (hd : 0 < U.dimension) :
    (toMergerAtom U hd).dimension = U.dimension + 1 :=
  U.dimension_toMerger (Nat.sub_add_cancel hd).symm

theorem pos_dimension_toMergerAtom (U : RoundShape) (hU : 0 < U.dimension) :
    0 < (toMergerAtom U hU).dimension := by
  rw [dimension_toMergerAtom]
  exact Nat.succ_pos _

theorem dimension_mergerAtom (U : RoundShape) (hd : 0 < U.dimension) :
    (mergerAtom U hd).dimension = U.dimension :=
  U.dimension_merger (Nat.sub_add_cancel hd).symm

theorem bdry_toMergerAtom (U : RoundShape) (hU : 0 < U.dimension) (α : Bool) :
    (toMergerAtom U hU).ogp.bdry ⊤ α =
      (toMergerAtom U hU).ogp.boundary ⊤ U.dimension α :=
  bdry_eq_boundary
    ((toMergerAtom U hU).toMoleculeShape.krullDim_top_eq (dimension_toMergerAtom U hU)) α

def mergerAtomBoundaryIso (U : RoundShape) (hU : 0 < U.dimension) (α : Bool) :
      ((mergerAtom U hU).toMoleculeShape.boundary (U.dimension - 1) α).ogp ≅
      (U.boundary (U.dimension - 1) α).ogp :=
  let hd : U.dimension = (U.dimension - 1) + 1 := (Nat.sub_add_cancel hU).symm
  let hd' : (mergerAtom U hU).toMoleculeShape.dimension = (U.dimension - 1) + 1 :=
    (dimension_mergerAtom U hU).trans hd
  ((mergerAtom U hU).toMoleculeShape.bdryIso hd' α) ≪≫
    (isoRestrictOfFintype (U.mergerIncl hd α) (U.map_mergerIncl hd α)).symm

theorem nonempty_iso_boundary_toMergerAtom (U : Atom) (hU : 0 < U.toRoundShape.dimension)
    (α : Bool) :
    Nonempty (((toMergerAtom U.toRoundShape hU).toMoleculeShape.boundary U.dimension α).ogp ≅
      U.ogp) := by
  let R := U.toRoundShape
  have hd : R.dimension = (U.dimension - 1) + 1 := (Nat.sub_add_cancel hU).symm
  have hdM : (toMergerAtom R hU).toMoleculeShape.dimension = U.dimension + 1 :=
    dimension_toMergerAtom R hU
  cases α
  · exact ⟨(toMergerAtom R hU).toMoleculeShape.bdryIso hdM false ≪≫
      (isoRestrictOfFintype (R.inputIncl hd) (R.map_inputIncl hd)).symm⟩
  · obtain ⟨θ⟩ := MoleculeShape.nonempty_iso_of_boundary_iso (mergerAtom R hU).toMoleculeShape
      R.toMoleculeShape (n := U.dimension - 1) (mergerAtomBoundaryIso R hU) (mergerAtom R hU).isAtom
      U.isAtom ((dimension_mergerAtom R hU).trans hd) hd
    exact ⟨(toMergerAtom R hU).toMoleculeShape.bdryIso hdM true ≪≫
      (isoRestrictOfFintype (R.outputIncl hd) (R.map_outputIncl hd)).symm ≪≫ θ⟩

def mergerAtomAll (U : RoundShape) : Atom :=
  if h : 0 < U.dimension then mergerAtom U h
  else Atom.ofIsAtom U.toFiniteOGP (U.isAtom_of_dimension_eq_zero (Nat.eq_zero_of_not_pos h))

theorem mergerAtomAll_of_pos (U : RoundShape) (h : 0 < U.dimension) :
    mergerAtomAll U = mergerAtom U h :=
  dif_pos h

theorem mergerAtomAll_of_eq_zero (U : RoundShape) (h : U.dimension = 0) :
    mergerAtomAll U = Atom.ofIsAtom U.toFiniteOGP (U.isAtom_of_dimension_eq_zero h) :=
  dif_neg (by omega)

theorem isAtom_unitShape (U : Atom) : IsAtom (unitShape U.toMoleculeShape).ogp := by
  have hnot : U.top ∉ U.ogp.bdryFull ⊤ := fun h => (U.mem_bdryFull_top_iff _).1 h rfl
  refine ⟨(unitShape U.toMoleculeShape).isMolecule, (cylShapeIso U.toMoleculeShape _).hom
    (PartialCylinder.mkI _ none U.top hnot), le_antisymm (fun a _ => ?_) le_top⟩
  rw [SetLike.mem_coe, LowerSet.mem_Iic_iff,
    ← Iso.inv_hom_id_apply (cylShapeIso U.toMoleculeShape _) a]
  exact (isMorphism (cylShapeIso U.toMoleculeShape _).hom).monotone
    (PartialCylinder.le_mkI_none_of_proj_le hnot (U.le_top _))

end Atoms.Shape
