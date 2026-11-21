import Atoms.Shape.Atom
import Atoms.Molecule.RegularComplex.CartesianAtom
import Mathlib.CategoryTheory.Category.Preorder

namespace Atoms.Shape

open CategoryTheory Order Set Atoms.Molecule Atoms.Molecule.OGP

def Atom.ofClosure (U : Atom) (x : U.ogp) : Atom :=
  Atom.ofOGP (U.ogp.restrict (.Iic x)) (IsAtomIn.isAtom_restrict ⟨U.isRDC x, x, rfl⟩)

def Atom.closureIso (U : Atom) (x : U.ogp) :
    U.ogp.restrict (.Iic x) ≅ (Atom.ofClosure U x).ogp :=
  U.subIso (U.isRDC x)

def Atom.closureInclOGP (U : Atom) (x : U.ogp) : (Atom.ofClosure U x).ogp ⟶ U.ogp :=
  U.subIncl (U.isRDC x)

instance (U : Atom) (x : U.ogp) : IsInclusion (Atom.closureInclOGP U x) :=
  inferInstanceAs (IsInclusion (U.subIncl (U.isRDC x)))

def Atom.closureIncl (U : Atom) (x : U.ogp) : Atom.ofClosure U x ⟶ U :=
  Atom.ofInclusion (Atom.closureInclOGP U x)

@[simp] theorem Atom.closureIncl_closureIso (U : Atom) (x : U.ogp)
    (y : U.ogp.restrict (.Iic x)) :
    Atom.closureIncl U x ((Atom.closureIso U x).hom y) = y.1 :=
  congrArg Subtype.val (ConcreteCategory.congr_hom (Atom.closureIso U x).hom_inv_id y)

theorem Atom.isInclusionHom_closureIncl (U : Atom) (x : U.ogp) :
    IsInclusionHom (Atom.closureIncl U x) :=
  IsInclusion.injective (f := Atom.closureInclOGP U x)

theorem Atom.exists_closureIncl_eq_iff (U : Atom) (x y : U.ogp) :
    (∃ w, Atom.closureIncl U x w = y) ↔ y ≤ x :=
  ⟨fun ⟨w, hw⟩ => hw ▸ ((Atom.closureIso U x).inv w).2,
    fun h => ⟨(Atom.closureIso U x).hom ⟨y, h⟩, Atom.closureIncl_closureIso U x ⟨y, h⟩⟩⟩

@[simp] theorem Atom.map_closureInclOGP_top (U : Atom) (x : U.ogp) :
    map (Atom.closureInclOGP U x) ⊤ = .Iic x :=
  U.map_subIncl_top (U.isRDC x)

theorem Atom.range_closureIncl (U : Atom) (x : U.ogp) :
    Set.range (Atom.closureIncl U x) = Set.Iic x := by
  ext y
  exact Atom.exists_closureIncl_eq_iff U x y

theorem Atom.top_ofClosure (U : Atom) (x : U.ogp) :
    (Atom.ofClosure U x).top = (Atom.closureIso U x).hom ⟨x, LowerSet.mem_Iic_iff.2 le_rfl⟩ := by
  refine le_antisymm ?_ ((Atom.ofClosure U x).le_top _)
  exact (orderIsoOfIso (Atom.closureIso U x)).symm_apply_le.1 ((Atom.closureIso U x).inv _).2

@[simp] theorem Atom.closureIncl_top (U : Atom) (x : U.ogp) :
    Atom.closureIncl U x (Atom.ofClosure U x).top = x := by
  rw [Atom.top_ofClosure, Atom.closureIncl_closureIso]

theorem Atom.dimension_ofClosure (U : Atom) (x : U.ogp) :
    (Atom.ofClosure U x).dimension = grade ℕ x := by
  have h := U.dimension_sub (U.isRDC x)
  rw [LowerSet.krullDim_Iic] at h
  exact_mod_cast h

theorem dimension_ofClosure_pos (U : Atom) (x : U.ogp) (hx : 0 < grade ℕ x) :
    0 < (Atom.ofClosure U x).dimension := by
  rw [Atom.dimension_ofClosure]
  exact hx

theorem image_boundary_closureIncl (U : Atom) (x : U.ogp) (k : ℕ) (α : Bool) :
    Atom.closureIncl U x '' ((Atom.ofClosure U x).ogp.boundary ⊤ k α : Set _) =
      U.ogp.boundary (.Iic x) k α :=
  congrArg SetLike.coe
    ((map_boundary (Atom.closureInclOGP U x) ⊤ k α).trans (by rw [Atom.map_closureInclOGP_top]))

theorem boundary_closure_nonempty (U : Atom) (x : U.ogp) (n : ℕ) (α : Bool) :
    ((U.ogp.boundary (.Iic x) n α : Set U.ogp)).Nonempty :=
  ((U.isRDC x).boundary n α).nonempty

theorem closureIncl_mem_closure (U : Atom) (x : U.ogp) (a : (Atom.ofClosure U x).ogp) :
    Atom.closureIncl U x a ∈ LowerSet.Iic x :=
  ((Atom.closureIso U x).inv a).2

theorem hom_ext_closureIncl (U : Atom) (x : U.ogp) {T : Atom}
    {g g' : T ⟶ Atom.ofClosure U x}
    (h : g ≫ Atom.closureIncl U x = g' ≫ Atom.closureIncl U x) : g = g' :=
  have := mono_of_isInclusionHom _ (Atom.isInclusionHom_closureIncl U x)
  (cancel_mono (Atom.closureIncl U x)).1 h

def principalLift (U : Atom) (x : U.ogp) {T : Atom} (f : T ⟶ U)
    (h : ∀ t, f t ∈ LowerSet.Iic x) : T ⟶ Atom.ofClosure U x :=
  InducedCategory.homMk (RDCpx.codRestrict f.hom (.Iic x) h ≫
    @RDCpx.ofInclusion (RDCpx.restrict U.rdc (.Iic x)) (Atom.ofClosure U x).rdc
      (Atom.closureIso U x).hom
      (@IsInclusion.of_isIso _ _ (Atom.closureIso U x).hom (Iso.isIso_hom (Atom.closureIso U x))))

@[simp] theorem principalLift_comp_closureIncl (U : Atom) (x : U.ogp)
    {T : Atom} (f : T ⟶ U) (h : ∀ t, f t ∈ LowerSet.Iic x) :
    principalLift U x f h ≫ Atom.closureIncl U x = f :=
  Atom.hom_ext fun t => Atom.closureIncl_closureIso U x ⟨f t, h t⟩

theorem apply_mem_closure_apply_top {T U : Atom} (f : T ⟶ U) (t : T.ogp) :
    f t ∈ LowerSet.Iic (f T.top) :=
  (Atom.isMap f).monotone (T.le_top t)

def principalMap (U : Atom) {x y : U.ogp} (hxy : x ≤ y) :
    Atom.ofClosure U x ⟶ Atom.ofClosure U y :=
  principalLift U y (Atom.closureIncl U x) fun a => (closureIncl_mem_closure U x a).trans hxy

@[simp] theorem principalMap_comp_closureIncl (U : Atom) {x y : U.ogp}
    (hxy : x ≤ y) : principalMap U hxy ≫ Atom.closureIncl U y = Atom.closureIncl U x :=
  principalLift_comp_closureIncl _ _ _ _

def principalDiagram (U : Atom) (S : Set U.ogp) : S ⥤ Atom where
  obj x := Atom.ofClosure U x.1
  map f := principalMap U (leOfHom f)
  map_id x := hom_ext_closureIncl U x.1 (by
    rw [principalMap_comp_closureIncl, Category.id_comp])
  map_comp f g := hom_ext_closureIncl U _ (by
    rw [principalMap_comp_closureIncl, Category.assoc,
      principalMap_comp_closureIncl, principalMap_comp_closureIncl])

theorem closureIncl_mem_of_closed (U : Atom) (S : LowerSet U.ogp) (x : S)
    (a : (Atom.ofClosure U x.1).ogp) : Atom.closureIncl U x.1 a ∈ S :=
  S.lower (closureIncl_mem_closure U x.1 a) x.2

theorem comp_closureIncl_mem (U : Atom) (S : LowerSet U.ogp) (x : S) {T : Atom}
    (g : T ⟶ Atom.ofClosure U x.1) (t : T.ogp) : (g ≫ Atom.closureIncl U x.1) t ∈ S :=
  closureIncl_mem_of_closed U S x (g t)

theorem principalLift_comp_principalMap (U : Atom) {x y : U.ogp} (hxy : x ≤ y)
    {T : Atom} (f : T ⟶ U) (h : ∀ t, f t ∈ LowerSet.Iic x)
    (h' : ∀ t, f t ∈ LowerSet.Iic y) :
    principalLift U x f h ≫ principalMap U hxy = principalLift U y f h' :=
  hom_ext_closureIncl U y (by
    rw [Category.assoc, principalMap_comp_closureIncl,
      principalLift_comp_closureIncl, principalLift_comp_closureIncl])

theorem isIso_principalLift_of_isInclusionHom {A W : Atom} (i : A ⟶ W)
    (hi : IsInclusionHom i) :
    CategoryTheory.IsIso (principalLift W (i A.top) i (apply_mem_closure_apply_top i)) := by
  refine isIso_of_isInclusionHom_of_dimension_eq _ (fun a b hab => hi ?_) ?_
  · exact Subtype.mk.inj ((IsInclusion.injective (f := (Atom.closureIso W (i A.top)).hom)) hab)
  · rw [A.dimension_eq, ← grade_eq_of_isInclusionHom i hi, Atom.dimension_ofClosure]

theorem mem_closure_apply_top_of_exists_eq {A W T : Atom} (i : A ⟶ W) {f : T ⟶ W}
    (h : ∀ t, ∃ a, i a = f t) (t : T.ogp) : f t ∈ LowerSet.Iic (i A.top) :=
  (h t).elim fun a ha => ha ▸ apply_mem_closure_apply_top i a

theorem exists_comp_eq_of_isInclusionHom {A W T : Atom} (i : A ⟶ W) (hi : IsInclusionHom i)
    (f : T ⟶ W) (h : ∀ t, ∃ a, i a = f t) : ∃ g : T ⟶ A, g ≫ i = f := by
  have := isIso_principalLift_of_isInclusionHom i hi
  have hc : inv (principalLift W (i A.top) i (apply_mem_closure_apply_top i)) ≫ i =
      Atom.closureIncl W (i A.top) :=
    (IsIso.inv_comp_eq _).2 (principalLift_comp_closureIncl W _ i _).symm
  refine ⟨principalLift W (i A.top) f (mem_closure_apply_top_of_exists_eq i h) ≫
    inv (principalLift W (i A.top) i (apply_mem_closure_apply_top i)), ?_⟩
  rw [Category.assoc, hc, principalLift_comp_closureIncl]

theorem principalLift_apply_top {T U : Atom} (f : T ⟶ U) :
    principalLift U (f T.top) f (apply_mem_closure_apply_top f) T.top =
      (Atom.ofClosure U (f T.top)).top := by
  apply Atom.isInclusionHom_closureIncl U (f T.top)
  rw [← ConcreteCategory.comp_apply, principalLift_comp_closureIncl, Atom.closureIncl_top]

theorem hom_apply_mem_closure_apply_top {T : Atom} {P : RDCpx.{0}}
    (f : atomToRDCpx.obj T ⟶ P) (t : T.ogp) :
    ConcreteCategory.hom f.hom t ∈ LowerSet.Iic (ConcreteCategory.hom f.hom T.top) :=
  (ConcreteCategory.hom f.hom).isMap.monotone (T.le_top t)

theorem apply_mem_of_apply_top_mem {T : Atom} {P : RDCpx.{0}}
    (f : atomToRDCpx.obj T ⟶ P) {S : LowerSet P.obj.toOGP}
    (h : ConcreteCategory.hom f.hom T.top ∈ S) (t : T.ogp) : ConcreteCategory.hom f.hom t ∈ S :=
  S.lower (hom_apply_mem_closure_apply_top f t) h

def restrictLift (P : RDCpx.{0}) (S : LowerSet P.obj.toOGP)
    {T : Atom} (f : atomToRDCpx.obj T ⟶ P) (h : ∀ t, ConcreteCategory.hom f.hom t ∈ S) :
    atomToRDCpx.obj T ⟶ RDCpx.restrict P S :=
  RDCpx.codRestrict f S h

def principalInclusionIn (U : Atom) (S : LowerSet U.ogp) {a : U.ogp} (ha : a ∈ S) :
    atomToRDCpx.obj (Atom.ofClosure U a) ⟶ RDCpx.restrict U.rdc S :=
  RDCpx.codRestrict (atomToRDCpx.map (Atom.closureIncl U a)) S
    fun t => S.lower (closureIncl_mem_closure U a t) ha

end Atoms.Shape
