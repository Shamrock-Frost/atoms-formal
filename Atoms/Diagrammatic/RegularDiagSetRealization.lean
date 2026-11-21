import Atoms.Diagrammatic.RegularDiagSet
import Mathlib.CategoryTheory.Subfunctor.OfSection

open CategoryTheory Limits Opposite Order Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

namespace DiagSet

variable {X : DiagSet.{u}}

theorem mem_ofSection_iff {U V : Atom} (x : diagram X U) (y : diagram X V) :
    y ∈ (Subfunctor.ofSection x).obj (op V) ↔ ∃ f : V ⟶ U, X.map f.op x = y :=
  ⟨fun ⟨f, hf⟩ => ⟨f.unop, hf⟩, fun ⟨f, hf⟩ => ⟨f.op, hf⟩⟩

theorem ofSection_map_le {U V : Atom} (f : V ⟶ U) (x : diagram X U) :
    Subfunctor.ofSection (X.map f.op x) ≤ Subfunctor.ofSection x :=
  (Subfunctor.ofSection_le_iff _ _).2 ((mem_ofSection_iff x _).2 ⟨f, rfl⟩)

theorem ofSection_map_of_isCollapseHom {U V : Atom} (p : V ⟶ U) (hp : IsCollapseHom p)
    (x : diagram X U) : Subfunctor.ofSection (X.map p.op x) = Subfunctor.ofSection x := by
  have := isSplitEpi_of_isCollapseHom p hp
  refine le_antisymm (ofSection_map_le p x) ((Subfunctor.ofSection_le_iff _ _).2
    ((mem_ofSection_iff _ _).2 ⟨section_ p, ?_⟩))
  rw [← Functor.map_comp_apply, ← op_comp, IsSplitEpi.id, op_id, Functor.map_id_apply]

abbrev RepresentableSubobject (X : DiagSet.{u}) : Type u :=
  {S : Subfunctor X // ∃ (U : Atom) (x : diagram X U), Subfunctor.ofSection x = S}

def faceSubobject {U : Atom} (x : diagram X U) (a : U.ogp) : RepresentableSubobject X :=
  ⟨Subfunctor.ofSection (X.map (Atom.closureIncl U a).op x), _, _, rfl⟩

@[simp] theorem coe_faceSubobject {U : Atom} (x : diagram X U) (a : U.ogp) :
    (faceSubobject x a : Subfunctor X) =
      Subfunctor.ofSection (X.map (Atom.closureIncl U a).op x) :=
  rfl

theorem ofSection_map {U W : Atom} (f : W ⟶ U) (x : diagram X U) :
    Subfunctor.ofSection (X.map f.op x) = faceSubobject x (f W.top) := by
  have h := principalLift_comp_closureIncl U (f W.top) f (apply_mem_closure_apply_top f)
  calc Subfunctor.ofSection (X.map f.op x)
      = Subfunctor.ofSection (X.map (principalLift U (f W.top) f
          (apply_mem_closure_apply_top f)).op (X.map (Atom.closureIncl U (f W.top)).op x)) := by
        rw [← Functor.map_comp_apply, ← op_comp, h]
    _ = _ := ofSection_map_of_isCollapseHom _
        (isCollapseHom_of_apply_eq_top _ (principalLift_apply_top f)) _

theorem faceSubobject_map {U W : Atom} (f : W ⟶ U) (x : diagram X U) (c : W.ogp) :
    faceSubobject (X.map f.op x) c = faceSubobject x (f c) := by
  refine Subtype.ext ?_
  rw [coe_faceSubobject, ← Functor.map_comp_apply, ← op_comp, ofSection_map,
    ConcreteCategory.comp_apply, Atom.closureIncl_top]

theorem coe_faceSubobject_top {U : Atom} (x : diagram X U) :
    (faceSubobject x U.top : Subfunctor X) = Subfunctor.ofSection x := by
  have h := ofSection_map (𝟙 U) x
  rw [op_id, Functor.map_id_apply, ConcreteCategory.id_apply] at h
  exact h.symm

theorem exists_faceSubobject_eq {U : Atom} (x : diagram X U) {S : RepresentableSubobject X}
    (hS : (S : Subfunctor X) ≤ Subfunctor.ofSection x) : ∃ a, faceSubobject x a = S := by
  obtain ⟨S, V, y, rfl⟩ := S
  obtain ⟨f, rfl⟩ := (mem_ofSection_iff x y).1 ((Subfunctor.ofSection_le_iff _ _).1 hS)
  exact ⟨f V.top, Subtype.ext (ofSection_map f x).symm⟩

theorem RepresentableSubobject.exists_cell (S : RepresentableSubobject X) :
    ∃ p : Σ U : Atom, diagram X U,
      ¬ IsDegenerate X p.2 ∧ Subfunctor.ofSection p.2 = (S : Subfunctor X) := by
  obtain ⟨S, U, x, rfl⟩ := S
  obtain ⟨V, p, y, hp, hy, rfl⟩ := Homotopical.EZCategory.exists_isNondegenerate X U x
  exact ⟨⟨V, y⟩, fun h => (isDegenerate_iff_not_isNondegenerate X y).1 h hy,
    (ofSection_map_of_isCollapseHom p (@isCollapseHom_of_isSplitEpi _ _ p hp) y).symm⟩

noncomputable def RepresentableSubobject.shape (S : RepresentableSubobject X) : Atom :=
  (Classical.choose S.exists_cell).1

noncomputable def RepresentableSubobject.cell (S : RepresentableSubobject X) :
    diagram X S.shape :=
  (Classical.choose S.exists_cell).2

theorem RepresentableSubobject.not_isDegenerate_cell (S : RepresentableSubobject X) :
    ¬ IsDegenerate X S.cell :=
  (Classical.choose_spec S.exists_cell).1

theorem RepresentableSubobject.ofSection_cell (S : RepresentableSubobject X) :
    Subfunctor.ofSection S.cell = (S : Subfunctor X) :=
  (Classical.choose_spec S.exists_cell).2

theorem RepresentableSubobject.faceSubobject_cell_top (S : RepresentableSubobject X) :
    faceSubobject S.cell S.shape.top = S :=
  Subtype.ext ((coe_faceSubobject_top S.cell).trans S.ofSection_cell)

theorem RepresentableSubobject.exists_faceSubobject_cell_eq {S T : RepresentableSubobject X}
    (h : S ≤ T) : ∃ a, faceSubobject T.cell a = S :=
  exists_faceSubobject_eq T.cell (T.ofSection_cell ▸ h)

private noncomputable def elementOf {S T : RepresentableSubobject X} (h : S ≤ T) : T.shape.ogp :=
  Classical.choose (RepresentableSubobject.exists_faceSubobject_cell_eq h)

private theorem faceSubobject_elementOf {S T : RepresentableSubobject X} (h : S ≤ T) :
    faceSubobject T.cell (elementOf h) = S :=
  Classical.choose_spec (RepresentableSubobject.exists_faceSubobject_cell_eq h)

theorem IsRegular.exists_iso_of_ofSection_eq (hX : X.IsRegular) {U V : Atom} {x : diagram X U}
    {y : diagram X V} (hx : ¬ IsDegenerate X x) (hy : ¬ IsDegenerate X y)
    (h : Subfunctor.ofSection x = Subfunctor.ofSection y) : ∃ e : U ≅ V, X.map e.hom.op y = x := by
  obtain ⟨g, hg⟩ := (mem_ofSection_iff y x).1 (h ▸ Subfunctor.mem_ofSection_obj x)
  obtain ⟨g', hg'⟩ := (mem_ofSection_iff x y).1 (h.symm ▸ Subfunctor.mem_ofSection_obj y)
  refine ⟨⟨g, g', hX.injective_map x hx U ?_, hX.injective_map y hy V ?_⟩, hg⟩
  · dsimp only
    rw [op_comp, Functor.map_comp_apply, hg', hg, op_id, Functor.map_id_apply]
  · dsimp only
    rw [op_comp, Functor.map_comp_apply, hg, hg', op_id, Functor.map_id_apply]

variable (hX : X.IsRegular)
include hX

theorem IsRegular.faceSubobject_le_faceSubobject_iff {U : Atom} {x : diagram X U}
    (hx : ¬ IsDegenerate X x) {a b : U.ogp} : faceSubobject x a ≤ faceSubobject x b ↔ a ≤ b := by
  constructor
  · intro h
    have h' := Subtype.coe_le_coe.2 h
    rw [coe_faceSubobject, coe_faceSubobject] at h'
    obtain ⟨g, hg⟩ := (mem_ofSection_iff _ _).1 ((Subfunctor.ofSection_le_iff _ _).1 h')
    have hgi : g ≫ Atom.closureIncl U b = Atom.closureIncl U a :=
      hX.injective_map x hx _ (by
        dsimp only
        rw [op_comp, Functor.map_comp_apply, hg])
    rw [← Atom.closureIncl_top U a, ← hgi, ConcreteCategory.comp_apply]
    exact closureIncl_mem_closure U b _
  · intro hab
    refine Subtype.coe_le_coe.1 ?_
    rw [coe_faceSubobject, coe_faceSubobject, ← principalMap_comp_closureIncl U hab, op_comp,
      Functor.map_comp_apply]
    exact ofSection_map_le _ _

def IsRegular.faceEmbedding {U : Atom} {x : diagram X U} (hx : ¬ IsDegenerate X x) :
    U.ogp ↪o RepresentableSubobject X :=
  OrderEmbedding.ofMapLEIff (faceSubobject x) fun _ _ => hX.faceSubobject_le_faceSubobject_iff hx

@[simp] theorem IsRegular.faceEmbedding_apply {U : Atom} {x : diagram X U}
    (hx : ¬ IsDegenerate X x) (a : U.ogp) : hX.faceEmbedding hx a = faceSubobject x a :=
  rfl

theorem IsRegular.range_faceEmbedding {U : Atom} {x : diagram X U} (hx : ¬ IsDegenerate X x) :
    Set.range (hX.faceEmbedding hx) = Set.Iic (faceSubobject x U.top) := by
  ext S
  refine ⟨?_, fun hS => exists_faceSubobject_eq x ?_⟩
  · rintro ⟨a, rfl⟩
    exact (hX.faceSubobject_le_faceSubobject_iff hx).2 (U.le_top a)
  · rw [← coe_faceSubobject_top x]
    exact hS

theorem IsRegular.faceSubobject_covBy_faceSubobject_iff {U : Atom} {x : diagram X U}
    (hx : ¬ IsDegenerate X x) {a b : U.ogp} : faceSubobject x a ⋖ faceSubobject x b ↔ a ⋖ b :=
  Set.OrdConnected.apply_covBy_apply_iff (hX.faceEmbedding hx)
    (by rw [hX.range_faceEmbedding hx]; exact Set.ordConnected_Iic)

theorem IsRegular.faceSubobject_cell_covBy_iff (T : RepresentableSubobject X) {a : T.shape.ogp} :
    faceSubobject T.cell a ⋖ T ↔ a ⋖ T.shape.top :=
  (Iff.of_eq (congrArg (faceSubobject T.cell a ⋖ ·) T.faceSubobject_cell_top)).symm.trans
    (hX.faceSubobject_covBy_faceSubobject_iff T.not_isDegenerate_cell)

theorem IsRegular.dimension_shape_faceSubobject {U : Atom} {x : diagram X U}
    (hx : ¬ IsDegenerate X x) (a : U.ogp) :
    (faceSubobject x a).shape.dimension = grade ℕ a := by
  obtain ⟨e, -⟩ := hX.exists_iso_of_ofSection_eq (faceSubobject x a).not_isDegenerate_cell
    (hX.not_isDegenerate_map x hx _ (Atom.isInclusionHom_closureIncl U a))
    (faceSubobject x a).ofSection_cell
  rw [Atom.dimension_eq_of_iso e, Atom.dimension_ofClosure]

@[implicit_reducible]
noncomputable def IsRegular.gradeMinOrder : GradeMinOrder ℕ (RepresentableSubobject X) where
  grade S := S.shape.dimension
  grade_strictMono S T h := by
    obtain ⟨a, rfl⟩ := RepresentableSubobject.exists_faceSubobject_cell_eq h.le
    beta_reduce
    rw [hX.dimension_shape_faceSubobject T.not_isDegenerate_cell, T.shape.dimension_eq]
    refine grade_strictMono (lt_of_le_of_ne (T.shape.le_top a) fun ha => h.ne ?_)
    rw [ha, T.faceSubobject_cell_top]
  covBy_grade S T h := by
    obtain ⟨a, rfl⟩ := RepresentableSubobject.exists_faceSubobject_cell_eq h.le
    rw [hX.dimension_shape_faceSubobject T.not_isDegenerate_cell, T.shape.dimension_eq]
    exact ((hX.faceSubobject_cell_covBy_iff T).1 h).grade ℕ
  isMin_grade S h := by
    rw [S.shape.dimension_eq]
    refine IsMin.grade ℕ fun b _ => ?_
    have hb : faceSubobject S.cell b ≤ faceSubobject S.cell S.shape.top :=
      (hX.faceSubobject_le_faceSubobject_iff S.not_isDegenerate_cell).2 (S.shape.le_top b)
    rw [S.faceSubobject_cell_top] at hb
    exact (hX.faceSubobject_le_faceSubobject_iff S.not_isDegenerate_cell).1
      (S.faceSubobject_cell_top.le.trans (h hb))

noncomputable def IsRegular.orient {S T : RepresentableSubobject X} (h : S ⋖ T) : Bool :=
  T.shape.ogp.orient ((hX.faceSubobject_cell_covBy_iff T).1
    ((congrArg (· ⋖ T) (faceSubobject_elementOf h.le)).mpr h))

theorem IsRegular.orient_eq {S T : RepresentableSubobject X} (h : S ⋖ T) {c : T.shape.ogp}
    (hc : faceSubobject T.cell c = S) (hcov : c ⋖ T.shape.top) :
    hX.orient h = T.shape.ogp.orient hcov :=
  orient_congr rfl ((hX.faceEmbedding T.not_isDegenerate_cell).injective
    ((faceSubobject_elementOf h.le).trans hc.symm)) _ _

theorem IsRegular.orient_faceSubobject {U : Atom} {x : diagram X U} (hx : ¬ IsDegenerate X x)
    {a b : U.ogp} (h : a ⋖ b) :
    hX.orient ((hX.faceSubobject_covBy_faceSubobject_iff hx).2 h) = U.ogp.orient h := by
  set T := faceSubobject x b
  obtain ⟨e, he⟩ := hX.exists_iso_of_ofSection_eq
    (hX.not_isDegenerate_map x hx _ (Atom.isInclusionHom_closureIncl U b)) T.not_isDegenerate_cell
    T.ofSection_cell.symm
  have key (d : (Atom.ofClosure U b).ogp) :
      faceSubobject T.cell (e.hom d) = faceSubobject x (Atom.closureIncl U b d) := by
    rw [← faceSubobject_map, he, faceSubobject_map]
  obtain ⟨d, hd⟩ := (Atom.exists_closureIncl_eq_iff U b a).2 h.le
  have hd' : d ⋖ (Atom.ofClosure U b).top :=
    (IsInclusion.covBy_iff (Atom.closureInclOGP U b)).1 (by
      have : Atom.closureIncl U b d ⋖ Atom.closureIncl U b (Atom.ofClosure U b).top := by
        rw [hd, Atom.closureIncl_top]
        exact h
      exact this)
  have htop : e.hom (Atom.ofClosure U b).top = T.shape.top := (isCollapseHom_of_iso e).apply_top
  have he' := Atom.isMorphism_of_isInclusionHom e.hom
    (Function.LeftInverse.injective (ConcreteCategory.congr_hom e.hom_inv_id))
  have hι := isMorphism (Atom.closureInclOGP U b)
  calc hX.orient _ = T.shape.ogp.orient (he'.covBy_apply hd') :=
        (hX.orient_eq _ ((key d).trans (congrArg _ hd)) (htop ▸ he'.covBy_apply hd')).trans
          (orient_congr htop.symm rfl _ _)
    _ = (Atom.ofClosure U b).ogp.orient hd' := he'.orient_apply hd'
    _ = U.ogp.orient (hι.covBy_apply hd') := (hι.orient_apply hd').symm
    _ = U.ogp.orient h := orient_congr (Atom.closureIncl_top U b) hd _ _

variable (X) in
@[implicit_reducible]
noncomputable def representableSubobjectsOGP : OGP.{u} where
  carrier := RepresentableSubobject X
  gradeMinOrderCarrier := hX.gradeMinOrder
  orient h := hX.orient h

theorem IsRegular.isMorphism_faceSubobject {U : Atom} {x : diagram X U}
    (hx : ¬ IsDegenerate X x) :
    IsMorphism (P := U.ogp) (Q := X.representableSubobjectsOGP hX) (faceSubobject x) := by
  refine ⟨fun a α => ⟨?_, (hX.faceEmbedding hx).injective.injOn, ?_⟩⟩
  · rintro c ⟨hc, rfl⟩
    exact ⟨(hX.faceSubobject_covBy_faceSubobject_iff hx).2 hc, hX.orient_faceSubobject hx hc⟩
  · rintro (S : RepresentableSubobject X) ⟨hS, rfl⟩
    have hle : (S : Subfunctor X) ≤ Subfunctor.ofSection x := by
      rw [← coe_faceSubobject_top x]
      exact Subtype.coe_le_coe.2
        (hS.le.trans ((hX.faceSubobject_le_faceSubobject_iff hx).2 (U.le_top a)))
    obtain ⟨c, rfl⟩ := exists_faceSubobject_eq x hle
    have hc := (hX.faceSubobject_covBy_faceSubobject_iff hx).1 hS
    exact ⟨c, ⟨hc, (hX.orient_faceSubobject hx hc).symm⟩, rfl⟩

end DiagSet

namespace DiagSet

variable {X : DiagSet.{0}} (hX : X.IsRegular)

noncomputable def IsRegular.faceInclusion {U : Atom} {x : diagram X U} (hx : ¬ IsDegenerate X x) :
    U.ogp ⟶ X.representableSubobjectsOGP hX :=
  ConcreteCategory.ofHom ⟨faceSubobject x, hX.isMorphism_faceSubobject hx⟩

@[simp] theorem IsRegular.faceInclusion_apply {U : Atom} {x : diagram X U}
    (hx : ¬ IsDegenerate X x) (a : U.ogp) : hX.faceInclusion hx a = faceSubobject x a :=
  rfl

instance IsRegular.isInclusion_faceInclusion {U : Atom} {x : diagram X U}
    (hx : ¬ IsDegenerate X x) : IsInclusion (hX.faceInclusion hx) :=
  ⟨(hX.faceEmbedding hx).injective⟩

theorem IsRegular.isRDC : (X.representableSubobjectsOGP hX).IsRDC := by
  intro (S : RepresentableSubobject X)
  have h := (isMoleculeIn_map_iff (hX.faceInclusion S.not_isDegenerate_cell)
    (.Iic S.shape.top)).2 (S.shape.isRDC S.shape.top)
  rwa [map_Iic, hX.faceInclusion_apply, S.faceSubobject_cell_top] at h

variable (X) in
@[implicit_reducible]
noncomputable def representableSubobjects : RDCpx.{0} :=
  ⟨⟨X.representableSubobjectsOGP hX, hX.isRDC⟩⟩

noncomputable def IsRegular.cellInclusion {U : Atom} {x : diagram X U}
    (hx : ¬ IsDegenerate X x) : atomToRDCpx.obj U ⟶ X.representableSubobjects hX :=
  @RDCpx.ofInclusion U.rdc (X.representableSubobjects hX) (hX.faceInclusion hx) _

private theorem exists_comp_ofInclusion_eq {P : RDCpx.{0}} {V W : Atom}
    (i : V.ogp ⟶ P.obj.toOGP) [IsInclusion i] (c : atomToRDCpx.obj W ⟶ P)
    (hc : ∀ w, ConcreteCategory.hom c.hom w ∈ map i ⊤) :
    ∃ g : W ⟶ V, atomToRDCpx.map g ≫ @RDCpx.ofInclusion V.rdc P i _ = c := by
  obtain ⟨e, he⟩ := RDCpx.exists_iso_restrict (U := V.rdc) (R := P) i
  refine ⟨Atom.fullyFaithful.preimage (RDCpx.codRestrict c _ hc ≫ e.inv), ?_⟩
  rw [Functor.FullyFaithful.map_preimage, Category.assoc, ← he, Iso.inv_hom_id_assoc,
    RDCpx.codRestrict_restrictIncl]

private theorem IsRegular.comp_cellInclusion_apply {V W : Atom} {x : diagram X V}
    (hx : ¬ IsDegenerate X x) (g : W ⟶ V) (w : W.ogp) :
    ConcreteCategory.hom (atomToRDCpx.map g ≫ hX.cellInclusion hx).hom w = faceSubobject x (g w) :=
  rfl

private theorem IsRegular.exists_comp_cellInclusion_eq {W : Atom}
    (c : atomToRDCpx.obj W ⟶ X.representableSubobjects hX) :
    ∃ (p : Σ V : Atom, diagram X V) (hp : ¬ IsDegenerate X p.2) (g : W ⟶ p.1),
      atomToRDCpx.map g ≫ hX.cellInclusion hp = c ∧ g W.top = p.1.top := by
  obtain ⟨S, hS⟩ : ∃ S : RepresentableSubobject X, ConcreteCategory.hom c.hom W.top = S :=
    ⟨_, rfl⟩
  obtain ⟨g, hg⟩ := exists_comp_ofInclusion_eq (hX.faceInclusion S.not_isDegenerate_cell) c
    fun w => by
      obtain ⟨a, ha⟩ : ConcreteCategory.hom c.hom w ∈ Set.range
          (hX.faceEmbedding S.not_isDegenerate_cell) := by
        rw [hX.range_faceEmbedding, S.faceSubobject_cell_top]
        exact ((ConcreteCategory.hom c.hom).isMap.monotone (W.le_top w)).trans hS.le
      exact ⟨a, LowerSet.mem_top, ha⟩
  refine ⟨⟨S.shape, S.cell⟩, S.not_isDegenerate_cell, g, hg,
    (hX.faceEmbedding S.not_isDegenerate_cell).injective ?_⟩
  rw [hX.faceEmbedding_apply, hX.faceEmbedding_apply, S.faceSubobject_cell_top]
  exact (hX.comp_cellInclusion_apply S.not_isDegenerate_cell g W.top).symm.trans
    ((congrArg (fun k : atomToRDCpx.obj W ⟶ X.representableSubobjects hX =>
      ConcreteCategory.hom k.hom W.top) hg).trans hS)

private theorem IsRegular.map_eq_of_comp_cellInclusion_eq {V V' W : Atom} {x : diagram X V}
    {x' : diagram X V'} (hx : ¬ IsDegenerate X x) (hx' : ¬ IsDegenerate X x') (j : V' ⟶ V)
    (hj : X.map j.op x = x') (g : W ⟶ V) (g' : W ⟶ V')
    (h : atomToRDCpx.map g ≫ hX.cellInclusion hx = atomToRDCpx.map g' ≫ hX.cellInclusion hx') :
    X.map g.op x = X.map g'.op x' := by
  have hg : g' ≫ j = g := Atom.hom_ext fun w => (hX.faceEmbedding hx).injective (by
    have h' := congrArg (fun k : atomToRDCpx.obj W ⟶ X.representableSubobjects hX =>
      ConcreteCategory.hom k.hom w) h
    rw [hX.faceEmbedding_apply, hX.faceEmbedding_apply, ConcreteCategory.comp_apply,
      ← faceSubobject_map, hj]
    exact h'.symm)
  rw [← hg, op_comp, Functor.map_comp_apply, hj]

private theorem IsRegular.exists_cell_of_hom {W : Atom}
    (c : atomToRDCpx.obj W ⟶ X.representableSubobjects hX) :
    ∃ y : diagram X W, ∀ {V : Atom} {x : diagram X V} (hx : ¬ IsDegenerate X x) (g : W ⟶ V),
      atomToRDCpx.map g ≫ hX.cellInclusion hx = c → X.map g.op x = y := by
  obtain ⟨⟨V₀, x₀⟩, hx₀, g₀, hg₀, htop⟩ := hX.exists_comp_cellInclusion_eq c
  refine ⟨X.map g₀.op x₀, fun {V x} hx g hg => ?_⟩
  have hle : Subfunctor.ofSection x₀ ≤ Subfunctor.ofSection x := by
    have h : faceSubobject x₀ (g₀ W.top) = faceSubobject x (g W.top) := by
      rw [← hX.comp_cellInclusion_apply hx₀, ← hX.comp_cellInclusion_apply hx, hg₀, hg]
    rw [← coe_faceSubobject_top x₀, ← coe_faceSubobject_top x, ← htop, h]
    exact Subtype.coe_le_coe.2 ((hX.faceSubobject_le_faceSubobject_iff hx).2 (V.le_top _))
  obtain ⟨j, hj⟩ := (mem_ofSection_iff x x₀).1 ((Subfunctor.ofSection_le_iff _ _).1 hle)
  exact hX.map_eq_of_comp_cellInclusion_eq hx hx₀ j hj g g₀ (hg.trans hg₀.symm)

private noncomputable def IsRegular.cellOf {W : Atom}
    (c : atomToRDCpx.obj W ⟶ X.representableSubobjects hX) : diagram X W :=
  Classical.choose (hX.exists_cell_of_hom c)

private theorem IsRegular.cellOf_comp_cellInclusion {V W : Atom} {x : diagram X V}
    (hx : ¬ IsDegenerate X x) (g : W ⟶ V) :
    hX.cellOf (atomToRDCpx.map g ≫ hX.cellInclusion hx) = X.map g.op x :=
  (Classical.choose_spec (hX.exists_cell_of_hom _) hx g rfl).symm

private theorem IsRegular.cellOf_comp {W W' : Atom} (f : W' ⟶ W)
    (c : atomToRDCpx.obj W ⟶ X.representableSubobjects hX) :
    hX.cellOf (atomToRDCpx.map f ≫ c) = X.map f.op (hX.cellOf c) := by
  obtain ⟨⟨V, x⟩, hx, g, rfl, -⟩ := hX.exists_comp_cellInclusion_eq c
  rw [← Category.assoc, ← Functor.map_comp, hX.cellOf_comp_cellInclusion,
    hX.cellOf_comp_cellInclusion, op_comp, Functor.map_comp_apply]

private theorem IsRegular.bijective_cellOf (W : Atom) :
    Function.Bijective fun c : ULift.{0} (atomToRDCpx.obj W ⟶ X.representableSubobjects hX) =>
      hX.cellOf c.down := by
  constructor
  · have key (c : atomToRDCpx.obj W ⟶ X.representableSubobjects hX) (w : W.ogp) :
        ConcreteCategory.hom c.hom w = faceSubobject (hX.cellOf c) w := by
      obtain ⟨⟨V, x⟩, hx, g, rfl, -⟩ := hX.exists_comp_cellInclusion_eq c
      rw [hX.cellOf_comp_cellInclusion, faceSubobject_map]
      rfl
    rintro ⟨c⟩ ⟨c'⟩ h
    refine congrArg ULift.up ?_
    ext w
    exact (key c w).trans ((congrArg (faceSubobject · w) h).trans (key c' w).symm)
  · intro y
    obtain ⟨V, p, x, -, hx, rfl⟩ := Homotopical.EZCategory.exists_isNondegenerate X W y
    have hx' : ¬ IsDegenerate X x := fun h => (isDegenerate_iff_not_isNondegenerate X x).1 h hx
    exact ⟨⟨atomToRDCpx.map p ≫ hX.cellInclusion hx'⟩, hX.cellOf_comp_cellInclusion hx' p⟩

noncomputable def IsRegular.isoRealize : X ≅ realize.{0}.obj (X.representableSubobjects hX) :=
  (NatIso.ofComponents
    (fun W => (Equiv.ofBijective _ (hX.bijective_cellOf W.unop)).toIso)
    (fun {W W'} f => by
      ext ⟨c⟩
      exact hX.cellOf_comp f.unop c)).symm

theorem IsRegular.isoRealize_inv_app {V W : Atom} {x : diagram X V} (hx : ¬ IsDegenerate X x)
    (g : W ⟶ V) :
    hX.isoRealize.inv.app (op W) ⟨atomToRDCpx.map g ≫ hX.cellInclusion hx⟩ = X.map g.op x :=
  hX.cellOf_comp_cellInclusion hx g

end DiagSet

theorem DiagSet.isRegular_iff_nonempty_iso_realize (X : DiagSet.{0}) :
    X.IsRegular ↔ ∃ P : RDCpx.{0}, Nonempty (X ≅ realize.{0}.obj P) :=
  ⟨fun hX => ⟨_, ⟨hX.isoRealize⟩⟩, fun ⟨P, ⟨e⟩⟩ => (isRegular_realize P).of_iso e.symm⟩

end Atoms.Diagrammatic
