import Atoms.Diagrammatic.BicategoryNerve.Composite
import Atoms.Diagrammatic.Rewriting.Path
import Atoms.Diagrammatic.Context.RoundBicategory

open CategoryTheory Opposite Order Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape
open CategoryTheory.Bicategory (PathCell pathComp pathComp_mapPath pathCompCompIso)
open CategoryTheory.FreeBicategory (lift IsStructural)
open scoped CategoryTheory.Bicategory

universe w v u v'

namespace Atoms.Diagrammatic

local instance (priority := high) instFintypeRdc (P : MoleculeShape) :
    Fintype P.rdc.obj.toOGP :=
  FinEnum.instFintype

namespace PastingDiagram

variable {B : Type u} [Bicategory.{w, v} B]

theorem toPath_heq {V : Type*} [Quiver V] {a b a' b' : V} {f : a ⟶ b} {f' : a' ⟶ b'}
    (ha : a = a') (hb : b = b') (h : f ≍ f') : f.toPath ≍ f'.toPath := by
  subst ha hb
  obtain rfl := eq_of_heq h
  rfl

theorem id_pathComp_heq {B : Type u} [Bicategory.{w, v} B] {a b a' b' : B}
    {p : Quiver.Path a b} {q : Quiver.Path a' b'}
    (ha : a = a') (hb : b = b') (h : p ≍ q) : 𝟙 (pathComp (𝟭q B) p) ≍ 𝟙 (pathComp (𝟭q B) q) := by
  subst ha hb
  obtain rfl := eq_of_heq h
  rfl

theorem obj_ofCell {U : Atom} (x : diagram (bicategoryNerve.{w, v, u} B) U) (y : U.ogp) :
    (bicategoryNerveHomEquiv B (ofCell x).shape.rdc (ofCell x).map).1.toPrefunctor.obj y =
      x.1.toPrefunctor.obj y := by
  have hx := congrArg (fun L => L.toPrefunctor.obj y) (cell_eq_comap_ofCell x)
  rw [Labelling.comap_obj] at hx
  exact hx.symm

theorem obj_vertex_of_equiv_boundary (d : PastingDiagram (bicategoryNerve.{w, v, u} B))
    (α : Bool) {x : diagram (bicategoryNerve.{w, v, u} B) atomPoint}
    (h : (d.boundary 0 α).Equiv (ofCell x)) {v : d.shape.rdc.obj.toOGP}
    (hv : d.shape.rdc.obj.toOGP.boundary ⊤ 0 α = .Iic v) :
    (bicategoryNerveHomEquiv B d.shape.rdc d.map).1.toPrefunctor.obj v =
      x.1.toPrefunctor.obj atomPoint.top := by
  have h₁ := bicategoryNerveHomEquiv_comp B (d.shape.boundaryInclRDC 0 α) d.map
  have h₂ := bicategoryNerveHomEquiv_comp B (RDCpx.isoOfIso (P := (d.boundary 0 α).shape.rdc)
    (Q := (ofCell x).shape.rdc) h.iso).hom (ofCell x).map
  rw [h.map_comm] at h₂
  have hmem : v ∈ OGP.map (d.shape.boundaryIncl 0 α) ⊤ := by
    rw [MoleculeShape.map_boundaryIncl_top]
    exact hv ▸ LowerSet.mem_Iic_iff.2 le_rfl
  obtain ⟨w', -, hw'⟩ := hmem
  have e := congrArg (fun L => L.toPrefunctor.obj w') (h₁.symm.trans h₂)
  rw [Labelling.comap_obj, Labelling.comap_obj] at e
  have hx := congrArg (fun L => L.toPrefunctor.obj atomPoint.top) (cell_eq_comap_ofCell x)
  rw [Labelling.comap_obj] at hx
  have hsub : Subsingleton atomPoint.ogp :=
    atomPoint.toMoleculeShape.subsingleton_of_dimension_eq_zero dimension_atomPoint
  refine (congrArg _ hw'.symm).trans (e.trans (Eq.trans ?_ hx.symm))
  exact congrArg _ (Subsingleton.elim (α := atomPoint.ogp) _ _)

theorem lift_map_homOfEq_id_heq {W : Type*} [Quiver W] (G : Prefunctor W B)
    {b c : FreeBicategory W} (h : b = c) :
    (lift G).map (Quiver.homOfEq (𝟙 b) rfl h) ≍ 𝟙 ((lift G).obj b) := by
  subst h
  rfl

theorem nerveComposite_unit_of_dim_eq_zero (m : PastingDiagram (bicategoryNerve.{w, v, u} B))
    (hm : m.dim = 0) (hd : m.unit.dim ≤ 2) {b : B}
    (h : m.nerveComposite (hm.trans_le (Nat.zero_le 2)) = ⟨b, b, .nil, .nil, 𝟙 _⟩) :
    m.unit.nerveComposite hd = ⟨b, b, (𝟙 b).toPath, (𝟙 b).toPath, 𝟙 _⟩ := by
  have hd₀ : m.shape.dimension = 0 := hm
  have hd₁ : m.unit.dim ≤ 1 := by
    rw [dim_unit]
    exact Nat.succ_le_succ hd₀.le
  have hM : IsMoleculeIn m.unit.shape.rdc.obj.toOGP ⊤ := m.unit.shape.isMolecule
  have hMm : IsMoleculeIn m.shape.rdc.obj.toOGP ⊤ := m.shape.isMolecule
  rw [nerveComposite_of_dim_le_one _ hd₁ hd (boundary_zero_eq_Iic_vertex _ hM false)
    (boundary_zero_eq_Iic_vertex _ hM true)]
  obtain ⟨-, c, hc⟩ := isAtom_unitShape_of_dimension_eq_zero m.shape hd₀
  have hgc : grade ℕ c = 1 := by
    have h₁ := m.unit.shape.krullDim_eq_dimension
    rw [← LowerSet.krullDim_top, hc, LowerSet.krullDim_Iic] at h₁
    have h' : m.unit.shape.dimension = 1 := (dim_unit m).trans (by rw [hm])
    exact_mod_cast h₁.trans (congrArg _ h')
  have hp := (pathOf_congr (P := m.unit.shape.rdc.obj.toOGP) (hU := hM)
    (hd := (m.unit.krullDim_top_le hd₁).trans_eq Nat.cast_one)
    (hdV := hc ▸ (m.unit.krullDim_top_le hd₁).trans_eq Nat.cast_one) (hV := hc ▸ hM)
    (hv := boundary_zero_eq_Iic_vertex _ hM false) (hw := boundary_zero_eq_Iic_vertex _ hM true)
    (hv' := hc ▸ boundary_zero_eq_Iic_vertex _ hM false)
    (hw' := hc ▸ boundary_zero_eq_Iic_vertex _ hM true) hc).trans
    (pathOf_Iic_of_grade_eq_one (P := m.unit.shape.rdc.obj.toOGP) hgc _ _ _ _)
  rw [hp, Prefunctor.mapPath_toPath]
  have hℓ : (bicategoryNerveHomEquiv B m.unit.shape.rdc m.unit.map).1 =
      (bicategoryNerveHomEquiv B m.shape.rdc m.map).1.comap
        (ConcreteCategory.hom (C := RDCpxDown) (cylProj m.shape
          (m.shape.ogp.bdryFull ⊤)).hom) m.unit.shape.rdc.obj.isRDC :=
    bicategoryNerveHomEquiv_comp B _ m.map
  rw [hℓ]
  have hsub : Subsingleton m.shape.rdc.obj.toOGP := m.shape.subsingleton_of_dimension_eq_zero hd₀
  have hb : (bicategoryNerveHomEquiv B m.shape.rdc m.map).1.toPrefunctor.obj
      (vertex ⊤ hMm false) = b := by
    have e := congrArg PathCell.src ((nerveComposite_of_dim_le_one m (by omega)
      (hm.trans_le (Nat.zero_le 2)) (boundary_zero_eq_Iic_vertex _ hMm false)
      (boundary_zero_eq_Iic_vertex _ hMm true)).symm.trans h)
    exact e
  have hobj (y : m.unit.shape.rdc.obj.toOGP) :
      ((bicategoryNerveHomEquiv B m.shape.rdc m.map).1.comap
        (ConcreteCategory.hom (C := RDCpxDown) (cylProj m.shape
          (m.shape.ogp.bdryFull ⊤)).hom) m.unit.shape.rdc.obj.isRDC).toPrefunctor.obj y = b :=
    (congrArg (bicategoryNerveHomEquiv B m.shape.rdc m.map).1.toPrefunctor.obj
      (Subsingleton.elim (α := m.shape.rdc.obj.toOGP) _ _)).trans hb
  have hg : grade ℕ ((ConcreteCategory.hom (C := RDCpxDown) (cylProj m.shape
      (m.shape.ogp.bdryFull ⊤)).hom) c) ≠ 1 := by
    have h1 := grade_le_krullDim ((ConcreteCategory.hom (C := RDCpxDown) (cylProj m.shape
      (m.shape.ogp.bdryFull ⊤)).hom) c)
    have h2 : krullDim m.shape.rdc.obj.toOGP = (m.shape.dimension : WithBot ℕ∞) :=
      m.shape.krullDim_eq_dimension
    rw [h2, hd₀] at h1
    have h3 : grade ℕ ((ConcreteCategory.hom (C := RDCpxDown) (cylProj m.shape
      (m.shape.ogp.bdryFull ⊤)).hom) c) ≤ 0 := by exact_mod_cast h1
    omega
  have hm₂ := (heq_of_eq (congrArg
    (lift (bicategoryNerveHomEquiv B m.shape.rdc m.map).1.toPrefunctor).map
    (Map.freePrefunctor_map_of_grade_ne (ConcreteCategory.hom (C := RDCpxDown) (cylProj
      m.shape (m.shape.ogp.bdryFull ⊤)).hom)
      (⟨c, hgc, by rw [← hc]; exact boundary_zero_eq_Iic_vertex _ hM false,
        by rw [← hc]; exact boundary_zero_eq_Iic_vertex _ hM true⟩ :
        Quiver.Hom (V := EdgeQuiver m.unit.shape.rdc.obj.toOGP) (vertex ⊤ hM false)
          (vertex ⊤ hM true)) hg))).trans ((lift_map_homOfEq_id_heq _ _).trans
      (congr_arg_heq (𝟙 ·) (hobj _)))
  have hm' := toPath_heq (hobj _) (hobj _) hm₂
  exact PathCell.ext (hobj _) (hobj _) hm' hm' (id_pathComp_heq (hobj _) (hobj _) hm')

theorem nerveComposite_unit_ofCell_point (x : diagram (bicategoryNerve.{w, v, u} B) atomPoint)
    (hd : (ofCell x).unit.dim ≤ 2) :
    (ofCell x).unit.nerveComposite hd =
      ⟨x.1.toPrefunctor.obj atomPoint.top, x.1.toPrefunctor.obj atomPoint.top,
        (𝟙 (x.1.toPrefunctor.obj atomPoint.top)).toPath,
        (𝟙 (x.1.toPrefunctor.obj atomPoint.top)).toPath, 𝟙 _⟩ := by
  have hd₀ : (ofCell x).dim = 0 := dimension_atomPoint
  have hM : IsMoleculeIn (ofCell x).shape.rdc.obj.toOGP ⊤ := (ofCell x).shape.isMolecule
  obtain ⟨b, hb⟩ := exists_nerveComposite_eq_of_dim_eq_zero (ofCell x)
    (hd₀.trans_le (Nat.zero_le 2)) hd₀
  have e := congrArg PathCell.src (hb.symm.trans (nerveComposite_of_dim_le_one (ofCell x)
    (hd₀.trans_le zero_le_one) _ (boundary_zero_eq_Iic_vertex _ hM false)
    (boundary_zero_eq_Iic_vertex _ hM true)))
  obtain rfl : b = x.1.toPrefunctor.obj atomPoint.top :=
    e.trans ((obj_ofCell x _).trans (congrArg _ (Subsingleton.elim (α := atomPoint.ogp)
      (h := atomPoint.toMoleculeShape.subsingleton_of_dimension_eq_zero dimension_atomPoint) _ _)))
  exact nerveComposite_unit_of_dim_eq_zero (ofCell x) hd₀ hd hb

private theorem conj_heq_id {C : Type*} [Category C] {W X Y Z : C} (e₁ : W = X) (φ : X ⟶ Y)
    (e₂ : Y = Z) (e₃ : X = Y) (hφ : φ ≍ 𝟙 X) : eqToHom e₁ ≫ φ ≫ eqToHom e₂ ≍ 𝟙 W := by
  subst e₁ e₃ e₂
  obtain rfl := eq_of_heq hφ
  simp only [eqToHom_refl, Category.id_comp]
  rfl

private theorem pathOf_heq {P : OGP.{0}} [Fintype P] [DecidableLE P] {U V : LowerSet P}
    [DecidablePred (· ∈ U)] [DecidablePred (· ∈ V)] (e : U = V) {hU : IsMoleculeIn P U}
    {hV : IsMoleculeIn P V} {hd : krullDim U ≤ 1} {hdV : krullDim V ≤ 1} {v w v' w' : P}
    (hv' : v = v') (hw' : w = w') {hv : P.boundary U 0 false = .Iic v}
    {hw : P.boundary U 0 true = .Iic w} {hv'' : P.boundary V 0 false = .Iic v'}
    {hw'' : P.boundary V 0 true = .Iic w'} :
    pathOf U hU hd hv hw ≍ pathOf V hV hdV hv'' hw'' := by
  subst hv' hw'
  exact heq_of_eq (pathOf_congr e)

private theorem pathComp_freePrefunctor_heq {P Q : OGP.{0}} (f : Map P Q) {a b a' b' : P}
    {p : Quiver.Path (V := EdgeQuiver P) a b} {q : Quiver.Path (V := EdgeQuiver P) a' b'}
    (ha : a = a') (hb : b = b') (h : p ≍ q) :
    pathComp f.freePrefunctor p ≍ pathComp f.freePrefunctor q := by
  subst ha hb
  obtain rfl := eq_of_heq h
  rfl

theorem nerveComposite_unit_of_dim_eq_one (m : PastingDiagram (bicategoryNerve.{w, v, u} B))
    (hm : m.dim = 1) (hd : m.unit.dim ≤ 2) {a b : B} {P : Quiver.Path a b}
    (h : m.nerveComposite (hm.trans_le one_le_two) = ⟨a, b, P, P, 𝟙 _⟩) :
    m.unit.nerveComposite hd = ⟨a, b, P, P, 𝟙 _⟩ := by
  have hb (α : Bool) : (m.unit.boundary 1 α).nerveComposite
      ((m.unit.shape.dimension_boundary_le 1 α).trans one_le_two) = ⟨a, b, P, P, 𝟙 _⟩ :=
    (nerveComposite_congr (boundary_unit hm α) _ _).trans h
  have h₀ := (nerveComposite_boundary_one m.unit hd false _).symm.trans (hb false)
  have h₁ := (nerveComposite_boundary_one m.unit hd true _).symm.trans (hb true)
  obtain ⟨hsrc, htgt, hdom, -, -⟩ := Bicategory.PathCell.mk.inj h₀
  obtain ⟨-, -, hcod, -, -⟩ := Bicategory.PathCell.mk.inj h₁
  simp only [cond_false] at hdom
  simp only [cond_true] at hcod
  refine Bicategory.PathCell.ext hsrc htgt hdom hcod ?_
  refine HEq.trans ?_ (id_pathComp_heq hsrc htgt hdom)
  have hM : IsMoleculeIn m.unit.shape.rdc.obj.toOGP ⊤ := m.unit.shape.isMolecule
  have hMm : IsMoleculeIn m.shape.rdc.obj.toOGP ⊤ := m.shape.isMolecule
  obtain ⟨xs, hxs⟩ := exists_isLayerOrder_of_krullDim_le hM (m.unit.krullDim_top_le hd)
  have hs := boundary_zero_eq_Iic_vertex _ hM false
  have ht := boundary_zero_eq_Iic_vertex _ hM true
  have hsm := boundary_zero_eq_Iic_vertex _ hMm false
  have htm := boundary_zero_eq_Iic_vertex _ hMm true
  have hdm : krullDim (⊤ : LowerSet m.shape.rdc.obj.toOGP) ≤ 1 :=
    (m.krullDim_top_le hm.le).trans_eq Nat.cast_one
  rw [nerveComposite_eq m.unit hd hs ht hxs]
  have hℓ : (bicategoryNerveHomEquiv B m.unit.shape.rdc m.unit.map).1 =
      (bicategoryNerveHomEquiv B m.shape.rdc m.map).1.comap
        (ConcreteCategory.hom (C := RDCpxDown) (cylProj m.shape (m.shape.ogp.bdryFull ⊤)).hom)
        m.unit.shape.rdc.obj.isRDC :=
    bicategoryNerveHomEquiv_comp B _ m.map
  rw [hℓ]
  dsimp only
  have hc (j : ℕ) (hj : j < xs.length) : grade ℕ ((ConcreteCategory.hom (C := RDCpxDown)
      (cylProj m.shape (m.shape.ogp.bdryFull ⊤)).hom) xs[j]) ≠ 2 := by
    have h1 := grade_le_krullDim ((ConcreteCategory.hom (C := RDCpxDown)
      (cylProj m.shape (m.shape.ogp.bdryFull ⊤)).hom) xs[j])
    have h2 : krullDim m.shape.rdc.obj.toOGP = (m.shape.dimension : WithBot ℕ∞) :=
      m.shape.krullDim_eq_dimension
    rw [h2] at h1
    have h3 : ((grade ℕ ((ConcreteCategory.hom (C := RDCpxDown) (cylProj m.shape
        (m.shape.ogp.bdryFull ⊤)).hom) xs[j]) : ℕ) : WithBot ℕ∞) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
      h1.trans (by exact_mod_cast hm.le)
    have h4 : grade ℕ ((ConcreteCategory.hom (C := RDCpxDown) (cylProj m.shape
        (m.shape.ogp.bdryFull ⊤)).hom) xs[j]) ≤ 1 := by exact_mod_cast h3
    omega
  have hS := Labelling.isStructural_compositeAlong (hP := m.unit.shape.rdc.obj.isRDC)
    (ConcreteCategory.hom (C := RDCpxDown)
    (cylProj m.shape (m.shape.ogp.bdryFull ⊤)).hom) (bicategoryNerveHomEquiv B m.shape.rdc m.map).1
    hM hxs hs ht hc
  have hX (α : Bool) : pathComp (ConcreteCategory.hom (C := RDCpxDown) (cylProj m.shape
      (m.shape.ogp.bdryFull ⊤)).hom).freePrefunctor
      (pathOf (m.unit.shape.rdc.obj.toOGP.boundary ⊤ 1 α) (hM.boundary 1 α)
        ((krullDim_boundary_le _ 1 α).trans_eq Nat.cast_one)
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans hs)
        ((hM.isGlobular.boundary_boundary_eq_of_le zero_le_one (.inl zero_lt_one)).trans ht)) ≍
      pathComp (Map.id m.shape.rdc.obj.toOGP).freePrefunctor (pathOf ⊤ hMm hdm hsm htm) := by
    have hK : OGP.map (P := m.shape.rdc.obj.toOGP) (Q := m.unit.shape.rdc.obj.toOGP)
        (cylEndpoint m.shape (m.shape.ogp.bdryFull ⊤) α) ⊤ =
        m.unit.shape.rdc.obj.toOGP.boundary ⊤ 1 α :=
      (map_cylEndpoint_bdryFull_top m.shape α).trans (by rw [← hm]; rfl)
    have hvert (β : Bool) {x : m.unit.shape.rdc.obj.toOGP} {y : m.shape.rdc.obj.toOGP}
        (hx : m.unit.shape.rdc.obj.toOGP.boundary ⊤ 0 β = .Iic x)
        (hy : m.shape.rdc.obj.toOGP.boundary ⊤ 0 β = .Iic y) :
        x = cylEndpoint m.shape (m.shape.ogp.bdryFull ⊤) α y := by
      have e : LowerSet.Iic x = .Iic (cylEndpoint m.shape (m.shape.ogp.bdryFull ⊤) α y) := by
        rw [← hx, ← hM.isGlobular.boundary_boundary_eq_of_le (α := β) (β := α) zero_le_one
          (.inl zero_lt_one), ← hK, ← map_Iic (P := m.shape.rdc.obj.toOGP)
          (Q := m.unit.shape.rdc.obj.toOGP), ← hy, map_boundary]
      exact LowerSet.Iic_injective e
    have hid : (ConcreteCategory.hom (C := RDCpxDown) (cylProj m.shape
        (m.shape.ogp.bdryFull ⊤)).hom).comp (⟨cylEndpoint m.shape (m.shape.ogp.bdryFull ⊤) α,
          isMap_of_isInclusion _⟩ : Map m.shape.rdc.obj.toOGP m.unit.shape.rdc.obj.toOGP) =
        Map.id m.shape.rdc.obj.toOGP :=
      Map.ext fun x => cylProj_cylEndpoint m.shape _ α x
    refine (pathComp_freePrefunctor_heq _ (hvert false hs hsm) (hvert true ht htm)
      (pathOf_heq hK.symm (hvert false hs hsm) (hvert true ht htm)
        (hV := (isMoleculeIn_map_iff _ ⊤).2 hMm) (hdV := (krullDim_map _ ⊤).trans_le hdm)
        (hv'' := (map_boundary _ ⊤ 0 false).symm.trans ((congrArg (OGP.map _) hsm).trans
          (map_Iic _ _)))
        (hw'' := (map_boundary _ ⊤ 0 true).symm.trans ((congrArg (OGP.map _) htm).trans
          (map_Iic _ _))))).trans ?_
    rw [← Map.mapPath_pathOf_of_isInclusion (P := m.shape.rdc.obj.toOGP)
      (Q := m.unit.shape.rdc.obj.toOGP), Map.pathComp_freePrefunctor_mapPath_of_isInclusion]
    exact congr_arg_heq (fun g : Map m.shape.rdc.obj.toOGP m.shape.rdc.obj.toOGP =>
      pathComp g.freePrefunctor (pathOf ⊤ hMm hdm hsm htm)) hid
  rw [eq_of_heq ((hX false).trans (hX true).symm)] at hS
  refine conj_heq_id _ _ _ ?_ ?_
  · obtain ⟨-, h₁, h₂, -⟩ := hS
    exact h₁.trans h₂
  · exact hS.heq_id

theorem nerveComposite_rounding_one {y : PastingDiagram (bicategoryNerve.{w, v, u} B)}
    (hy : y.dim = 2) (hd : (y.rounding 1).dim ≤ 2) {a b : B} {P Q : Quiver.Path a b}
    {φ : pathComp (𝟭q B) P ⟶ pathComp (𝟭q B) Q} (h : y.nerveComposite hy.le = ⟨a, b, P, Q, φ⟩) :
    (y.rounding 1).nerveComposite hd = ⟨a, b, P, Q, φ⟩ := by
  have hk : 1 < y.dim := by omega
  have hq := pastable_unit_boundary hk
  have hb1 : (y.boundary 1 true).dim = 1 := dim_boundary y hk.le true
  have hb : (y.boundary 1 true).nerveComposite (hb1.trans_le one_le_two) = ⟨a, b, Q, Q, 𝟙 _⟩ := by
    rw [nerveComposite_boundary_one y hy.le true, h]
    rfl
  have hud : (y.boundary 1 true).unit.dim ≤ 2 := by rw [dim_unit, hb1]
  have hpd : (y.paste (y.boundary 1 true).unit 1 hq).dim ≤ 2 := by
    rw [dim_paste, dim_unit, hb1, hy]
    exact (max_self 2).le
  refine (nerveComposite_congr (equiv_of_eq (rounding_eq hk)) hd hpd).trans ?_
  refine (nerveComposite_pasteAlong_one _ _ hq.1.iso hq.1.map_comm hy.le hud hpd h
    (nerveComposite_unit_of_dim_eq_one _ hb1 hud hb)).trans ?_
  rw [Category.comp_id]

theorem nerveComposite_rounding_paste_left {u w : PastingDiagram (bicategoryNerve.{w, v, u} B)}
    (hp : u.Pastable w 0) (hu : u.dim = 1) (hw : w.dim = 2)
    (hd : ((u.paste w 0 hp).rounding 1).dim ≤ 2) {a b c : B} {P : Quiver.Path a b}
    {Q R : Quiver.Path b c} {φ : pathComp (𝟭q B) Q ⟶ pathComp (𝟭q B) R}
    (hx : u.nerveComposite (hu.trans_le one_le_two) = ⟨a, b, P, P, 𝟙 _⟩)
    (hy : w.nerveComposite hw.le = ⟨b, c, Q, R, φ⟩) :
    ((u.paste w 0 hp).rounding 1).nerveComposite hd =
      ⟨a, c, P.comp Q, P.comp R, (pathCompCompIso (𝟭q B) P Q).hom ≫ pathComp (𝟭q B) P ◁ φ ≫
        (pathCompCompIso (𝟭q B) P R).inv⟩ := by
  have hyd : (u.paste w 0 hp).dim = 2 := by rw [dim_paste, hu, hw]; rfl
  have e := nerveComposite_pasteAlong_zero u w hp.1.iso hp.1.map_comm _ _ hyd.le hx hy
  rw [Bicategory.id_whiskerRight, Category.id_comp] at e
  exact nerveComposite_rounding_one hyd hd e

theorem nerveComposite_rounding_paste_right {w z : PastingDiagram (bicategoryNerve.{w, v, u} B)}
    (hp : w.Pastable z 0) (hw : w.dim = 2) (hz : z.dim = 1)
    (hd : ((w.paste z 0 hp).rounding 1).dim ≤ 2) {a b c : B} {P Q : Quiver.Path a b}
    {R : Quiver.Path b c} {φ : pathComp (𝟭q B) P ⟶ pathComp (𝟭q B) Q}
    (hy : w.nerveComposite hw.le = ⟨a, b, P, Q, φ⟩)
    (hx : z.nerveComposite (hz.trans_le one_le_two) = ⟨b, c, R, R, 𝟙 _⟩) :
    ((w.paste z 0 hp).rounding 1).nerveComposite hd =
      ⟨a, c, P.comp R, Q.comp R, (pathCompCompIso (𝟭q B) P R).hom ≫ φ ▷ pathComp (𝟭q B) R ≫
        (pathCompCompIso (𝟭q B) Q R).inv⟩ := by
  have hyd : (w.paste z 0 hp).dim = 2 := by rw [dim_paste, hz, hw]; rfl
  have e := nerveComposite_pasteAlong_zero w z hp.1.iso hp.1.map_comm _ _ hyd.le hy hx
  rw [Bicategory.whiskerLeft_id, Category.comp_id] at e
  exact nerveComposite_rounding_one hyd hd e

theorem nerveComposite_unit_paste {m y : PastingDiagram (bicategoryNerve.{w, v, u} B)}
    (hm : m.dim = 1) (hy : y.dim = 2) (hp : m.unit.Pastable y 1)
    (hd : (m.unit.paste y 1 hp).dim ≤ 2) {a b : B} {P Q : Quiver.Path a b}
    {φ : pathComp (𝟭q B) P ⟶ pathComp (𝟭q B) Q} (h : y.nerveComposite hy.le = ⟨a, b, P, Q, φ⟩) :
    (m.unit.paste y 1 hp).nerveComposite hd = ⟨a, b, P, Q, φ⟩ := by
  have hb1 : (y.boundary 1 false).dim ≤ 2 :=
    (y.shape.dimension_boundary_le 1 false).trans one_le_two
  have hmb : m.Equiv (y.boundary 1 false) := (boundary_unit hm true).symm.trans hp.1
  have hc : m.nerveComposite (hm.trans_le one_le_two) = ⟨a, b, P, P, 𝟙 _⟩ := by
    rw [nerveComposite_congr hmb _ hb1, nerveComposite_boundary_one y hy.le false, h]
    rfl
  have hud : m.unit.dim ≤ 2 := by rw [dim_unit, hm]
  refine (nerveComposite_pasteAlong_one _ _ hp.1.iso hp.1.map_comm hud hy.le hd
    (nerveComposite_unit_of_dim_eq_one m hm hud hc) h).trans ?_
  rw [Category.id_comp]

theorem equiv_reverse_factorization {X : DiagSet.{u}} (u : PastingDiagram X) (hu : u.IsDegenerate)
    (f : DegeneracyFactorization u)
    (hJ : ∀ x : f.target.obj.toOGP, OGP.topDim u.shape.dimension (grade ℕ x) = false) :
    (u.reverse hu).Equiv ⟨u.shape.dual (OGP.topDim u.shape.dimension),
      realize.map (MoleculeShape.dualLift f.proj hJ) ≫ f.map⟩ := by
  have : Finite f.target.obj.toOGP := Finite.of_surjective _ f.surjective
  have : Finite hu.factorization.target.obj.toOGP :=
    Finite.of_surjective _ hu.factorization.surjective
  refine ⟨Iso.refl _, ?_⟩
  change realize.map (𝟙 _) ≫ _ = _
  rw [realize.map_id, Category.id_comp]
  refine realize_map_comp_eq_of_apply_eq (U := u.shape.rdc)
    (R := (u.shape.dual (OGP.topDim u.shape.dimension)).rdc) f.proj hu.factorization.proj f.map
    hu.factorization.map (f.comp_eq.trans hu.factorization.comp_eq.symm)
    (fun y => (u.shape.dualIso _).inv y)
    (fun x y hxy => (isMorphism (u.shape.dualIso _).inv).monotone hxy) _ _ (fun _ => rfl)
    (fun _ => rfl)

theorem pathCell_exists_eq_mk {B : Type u} [Bicategory.{w, v} B] (C : PathCell B)
    {a b : B} {P Q : Quiver.Path a b}
    (ha : C.src = a) (hb : C.tgt = b) (hP : C.dom ≍ P) (hQ : C.cod ≍ Q) :
    ∃ φ, C = ⟨a, b, P, Q, φ⟩ := by
  obtain ⟨a', b', P', Q', φ⟩ := C
  dsimp only at ha hb hP hQ
  subst ha hb
  obtain rfl := eq_of_heq hP
  obtain rfl := eq_of_heq hQ
  exact ⟨φ, rfl⟩

theorem exists_isStructural_of_equiv_freeImage {R : OGP.{0}} (F : Prefunctor (EdgeQuiver R) B)
    {D M : MoleculeShape} (g : D.rdc ⟶ M.rdc) (φ : realize.obj M.rdc ⟶ bicategoryNerve B)
    (φ' : realize.obj M.rdc ⟶ bicategoryNerve.{0, 0, 0} (FreeBicategory (EdgeQuiver R)))
    (h : (bicategoryNerveHomEquiv B M.rdc φ).1.toPrefunctor =
      (bicategoryNerveHomEquiv _ M.rdc φ').1.toPrefunctor ⋙q (lift F).toPrefunctor)
    (hM : M.dimension ≤ 1) {dB : PastingDiagram (bicategoryNerve.{w, v, u} B)}
    {dF : PastingDiagram (bicategoryNerve.{0, 0, 0} (FreeBicategory (EdgeQuiver R)))}
    (hB : dB.Equiv ⟨D, realize.map g ≫ φ⟩) (hF : dF.Equiv ⟨D, realize.map g ≫ φ'⟩)
    (hdB : dB.dim ≤ 2) (hdF : dF.dim ≤ 2) {a b : B} {P Q : Quiver.Path a b}
    {θ : pathComp (𝟭q B) P ⟶ pathComp (𝟭q B) Q} (hθ : dB.nerveComposite hdB = ⟨a, b, P, Q, θ⟩)
    {a' b' : FreeBicategory (EdgeQuiver R)} {P' Q' : Quiver.Path a' b'}
    {θ' : pathComp (𝟭q _) P' ⟶ pathComp (𝟭q _) Q'}
    (hθ' : dF.nerveComposite hdF = ⟨a', b', P', Q', θ'⟩) :
    ∃ ψ : pathComp (𝟭q B) ((lift F).toPrefunctor.mapPath P') ⟶
        pathComp (𝟭q B) ((lift F).toPrefunctor.mapPath Q'),
      IsStructural F (pathComp (𝟭q _) P') (pathComp (𝟭q _) Q') ψ ∧ θ ≍ ψ := by
  have hD : (⟨D, realize.map g ≫ φ⟩ : PastingDiagram (bicategoryNerve.{w, v, u} B)).dim ≤ 2 :=
    (dim_eq_of_equiv hB) ▸ hdB
  obtain ⟨ψ, hψ, he⟩ := nerveComposite_of_freeImage F g φ φ' h hM hD
    ((nerveComposite_congr hF.symm _ hdF).trans hθ')
  obtain ⟨-, -, -, -, hh⟩ := Bicategory.PathCell.mk.inj (hθ.symm.trans
    ((nerveComposite_congr hB hdB hD).trans he))
  exact ⟨ψ, hψ, hh⟩

theorem mk_realize_eq {X : DiagSet.{u}} {D D' : MoleculeShape} {M : RDCpx.{0}} (hD : D = D')
    {g : D.rdc ⟶ M} {g' : D'.rdc ⟶ M} (hg : g ≍ g') (φ : realize.obj M ⟶ X) :
    (⟨D, realize.map g ≫ φ⟩ : PastingDiagram X) = ⟨D', realize.map g' ≫ φ⟩ := by
  subst hD
  obtain rfl := eq_of_heq hg
  rfl

end PastingDiagram

section Tautological

theorem grade_le_of_dimension_le (P : MoleculeShape) {n : ℕ} (h : P.dimension ≤ n)
    (x : P.ogp) : grade ℕ x ≤ n := by
  have h₁ := grade_le_krullDim x
  have h₂ : krullDim P.ogp = (P.dimension : WithBot ℕ∞) := P.krullDim_eq_dimension
  rw [h₂] at h₁
  have h₃ : ((grade ℕ x : ℕ) : WithBot ℕ∞) ≤ ((n : ℕ) : WithBot ℕ∞) :=
    h₁.trans (by exact_mod_cast h)
  exact_mod_cast h₃

private theorem grade_ne_two_of_dimension_le_one {U : Atom} (hU : U.dimension ≤ 1) (x : U.ogp) :
    grade ℕ x ≠ 2 := by
  have := U.grade_le_dimension x
  omega

def tautLabelling (U : Atom) (hU : U.dimension ≤ 1) :
    Labelling (FreeBicategory (EdgeQuiver U.ogp)) U.ogp U.isRDC :=
  Labelling.free (grade_ne_two_of_dimension_le_one hU)

theorem isCommutative_tautLabelling (U : Atom) (hU : U.dimension ≤ 1) :
    (tautLabelling U hU).IsCommutative := fun y hy =>
  absurd ((U.grade_le_dimension y).trans hU) (by omega)

def tautCell (U : Atom) (hU : U.dimension ≤ 1) :
    diagram (bicategoryNerve.{_, _, 0} (FreeBicategory (EdgeQuiver U.ogp))) U :=
  ⟨tautLabelling U hU, isCommutative_tautLabelling U hU⟩

variable {B : Type u} [Bicategory.{w, v} B]

def pointLabelling (b : B) : Labelling B atomPoint.ogp atomPoint.isRDC where
  toPrefunctor :=
    { obj _ := b
      map e := absurd (atomPoint.grade_le_dimension e.1) (by
        rw [dimension_atomPoint, e.2.1]
        omega) }
  obj_eq_of_boundary_Iic _ _ _ := rfl
  cell x hx := absurd (atomPoint.grade_le_dimension x) (by
    rw [dimension_atomPoint, hx]
    omega)

def nervePointCell (b : B) : diagram (bicategoryNerve.{w, v, u} B) atomPoint :=
  ⟨pointLabelling b, fun y hy => absurd (atomPoint.grade_le_dimension y) (by
    rw [dimension_atomPoint, hy]
    omega)⟩

theorem toPrefunctor_ofCell {U : Atom} (x : diagram (bicategoryNerve.{w, v, u} B) U) :
    (bicategoryNerveHomEquiv B (PastingDiagram.ofCell x).shape.rdc
      (PastingDiagram.ofCell x).map).1.toPrefunctor = x.1.toPrefunctor := by
  refine Prefunctor.hext (fun y => PastingDiagram.obj_ofCell x y) fun y z d => ?_
  have hx := congr_arg_heq (fun L : Labelling B U.ogp U.isRDC => L.toPrefunctor.map d)
    (PastingDiagram.cell_eq_comap_ofCell x)
  refine HEq.trans ?_ hx.symm
  have hd : grade ℕ d.1 = 1 := d.2.1
  refine heq_of_eq ?_
  simp only [Labelling.comap, Prefunctor.comp_map]
  rw [Map.freePrefunctor_map_of_grade_eq _ d hd]
  rfl

private theorem boundaryIncl_zero_apply {X : DiagSet.{u}} (d : PastingDiagram X) (α : Bool)
    {v : d.shape.ogp} (hv : d.shape.ogp.boundary ⊤ 0 α = .Iic v)
    (w : (d.shape.boundary 0 α).ogp) : d.shape.boundaryIncl 0 α w = v := by
  have hmem : v ∈ OGP.map (d.shape.boundaryIncl 0 α) ⊤ := by
    rw [MoleculeShape.map_boundaryIncl_top]
    exact hv ▸ LowerSet.mem_Iic_iff.2 le_rfl
  obtain ⟨w', -, hw'⟩ := hmem
  have : Subsingleton (d.shape.boundary 0 α).ogp :=
    (d.shape.boundary 0 α).subsingleton_of_dimension_eq_zero
      (Nat.le_zero.1 (d.shape.dimension_boundary_le 0 α))
  exact (congrArg _ (Subsingleton.elim w w')).trans hw'

theorem equiv_boundary_tautCell {U : Atom} (hU : U.dimension = 1) {X : DiagSet.{u}}
    {x : diagram X U} {p : diagram X atomPoint} (β : Bool)
    (hx : ((PastingDiagram.ofCell x).boundary 0 β).Equiv (PastingDiagram.ofCell p)) :
    ((PastingDiagram.ofCell (tautCell U hU.le)).boundary 0 β).Equiv
      (PastingDiagram.ofCell (nervePointCell.{0, 0, 0}
        (vertex (.Iic U.top) (U.isRDC _) β : FreeBicategory (EdgeQuiver U.ogp)))) := by
  refine ⟨hx.iso, (bicategoryNerveHomEquiv _ _).injective (Subtype.ext ?_)⟩
  rw [bicategoryNerveHomEquiv_comp]
  have h₁ := bicategoryNerveHomEquiv_comp (FreeBicategory (EdgeQuiver U.ogp))
    ((PastingDiagram.ofCell (tautCell U hU.le)).shape.boundaryInclRDC 0 β)
    (PastingDiagram.ofCell (tautCell U hU.le)).map
  refine Eq.trans ?_ h₁.symm
  have hv : U.ogp.boundary ⊤ 0 β = .Iic (vertex (.Iic U.top) (U.isRDC _) β) :=
    (congrArg (fun V => U.ogp.boundary V 0 β) (Atom.Iic_top U)).symm.trans
      (boundary_zero_eq_Iic_vertex _ _ β)
  refine Labelling.ext (Prefunctor.hext (fun w => ?_) fun y z d => ?_) fun y hy => ?_
  · have key : ConcreteCategory.hom (C := RDCpxDown)
        ((PastingDiagram.ofCell (tautCell U hU.le)).shape.boundaryInclRDC 0 β).hom w =
        vertex (.Iic U.top) (U.isRDC _) β :=
      boundaryIncl_zero_apply (PastingDiagram.ofCell (tautCell U hU.le)) β hv w
    rw [Labelling.comap_obj, Labelling.comap_obj, PastingDiagram.obj_ofCell,
      PastingDiagram.obj_ofCell, key]
    exact (vertex_Iic_of_boundary_Iic (boundary_zero_eq_Iic_vertex _ (U.isRDC _) β)
      (U.isRDC _)).symm
  · have := grade_le_of_dimension_le _
      ((PastingDiagram.ofCell (tautCell U hU.le)).shape.dimension_boundary_le 0 β) d.1
    have h1 : grade ℕ d.1 = 1 := d.2.1
    omega
  · have := grade_le_of_dimension_le _
      ((PastingDiagram.ofCell (tautCell U hU.le)).shape.dimension_boundary_le 0 β) y
    omega

def edgeSig : Layered.Signature.{0} :=
  ⟨Bool, Unit, Empty, fun _ => false, fun _ => true, fun e => e.elim, fun e => e.elim⟩

instance : DecidableEq edgeSig.Pt := inferInstanceAs (DecidableEq Bool)

instance : DecidableEq edgeSig.Ed := inferInstanceAs (DecidableEq Unit)

theorem wellFormed_edgeSig : edgeSig.WellFormed := fun c => Empty.elim c

def freeEdgeInterp {U : Atom} (hU : U.dimension = 1) {X : DiagSet.{u}} {x : diagram X U}
    {p : Bool → diagram X atomPoint}
    (hx : ∀ β, ((PastingDiagram.ofCell x).boundary 0 β).Equiv (PastingDiagram.ofCell (p β))) :
    edgeSig.PathInterp (bicategoryNerve.{0, 0, 0} (FreeBicategory (EdgeQuiver U.ogp))) where
  point b := nervePointCell (vertex (.Iic U.top) (U.isRDC _) b : FreeBicategory (EdgeQuiver U.ogp))
  edge _ := ⟨U, tautCell U hU.le⟩
  hasRoundType_edge _ := .of_equiv_boundary dimension_atomPoint dimension_atomPoint
    hU fun β => by
      cases β
      · exact equiv_boundary_tautCell hU false (hx false)
      · exact equiv_boundary_tautCell hU true (hx true)

def pointSig : Layered.Signature.{0} :=
  ⟨Unit, Empty, Empty, Empty.elim, Empty.elim, Empty.elim, Empty.elim⟩

instance : DecidableEq pointSig.Pt := inferInstanceAs (DecidableEq Unit)

instance : DecidableEq pointSig.Ed := inferInstanceAs (DecidableEq Empty)

theorem wellFormed_pointSig : pointSig.WellFormed := fun c => Empty.elim c

def freePointInterp :
    pointSig.PathInterp
      (bicategoryNerve.{0, 0, 0} (FreeBicategory (EdgeQuiver atomPoint.ogp))) where
  point _ := tautCell atomPoint (dimension_atomPoint.trans_le zero_le_one)
  edge e := Empty.elim e
  hasRoundType_edge e := Empty.elim e

end Tautological

section LocallyDiscrete

private theorem exists_boundary_top_eq_Iic {U : Atom} (hU : U.dimension = 1) {v : U.ogp}
    (hv : grade ℕ v = 0) : ∃ β, U.ogp.boundary (.Iic U.top) 0 β = .Iic v := by
  have hg : grade ℕ U.top = 1 := U.dimension_eq.symm.trans hU
  have hle : v ≤ U.top := LowerSet.mem_Iic_iff.1 (U.Iic_top ▸ LowerSet.mem_top)
  have hc : v ⋖ U.top := GradeOrder.covBy_of_le_of_grade_eq_add_one hle (by omega)
  exact ⟨U.ogp.orient hc, (mem_faces_iff_boundary_Iic_eq (U.isRDC _) hg _).1 ⟨hc, rfl⟩⟩

private theorem locallyDiscrete_ext {X : Type u} {a b : LocallyDiscrete (Discrete X)}
    (h : a.as.as = b.as.as) : a = b := by
  obtain ⟨⟨a⟩⟩ := a
  obtain ⟨⟨b⟩⟩ := b
  cases h
  rfl

theorem bijective_obj_top_locallyDiscrete {X : Type u} {U : Atom} (hU : U.dimension = 1) :
    Function.Bijective fun c : diagram (bicategoryNerve (LocallyDiscrete (Discrete X))) U =>
      (c.1.toPrefunctor.obj U.top).as.as := by
  have hg : grade ℕ U.top = 1 := U.dimension_eq.symm.trans hU
  have key (c : diagram (bicategoryNerve (LocallyDiscrete (Discrete X))) U) {v : U.ogp}
      (hv : grade ℕ v = 0) : c.1.toPrefunctor.obj v = c.1.toPrefunctor.obj U.top := by
    obtain ⟨β, hβ⟩ := exists_boundary_top_eq_Iic hU hv
    obtain rfl := vertex_eq_of_boundary_zero_eq_Iic _ (U.isRDC _) hβ
    rw [c.1.obj_eq_obj_vertex U.top]
    have e : Quiver.Hom (V := EdgeQuiver U.ogp) (vertex (.Iic U.top) (U.isRDC _) false)
        (vertex (.Iic U.top) (U.isRDC _) true) :=
      ⟨U.top, hg, boundary_zero_eq_Iic_vertex _ _ false, boundary_zero_eq_Iic_vertex _ _ true⟩
    have h01 := Discrete.eq_of_hom (c.1.toPrefunctor.map e).as
    cases β
    · rfl
    · exact locallyDiscrete_ext h01.symm
  refine ⟨fun c c' h => Subtype.ext (Labelling.ext_of_grade_eq_zero
    (fun v hv => (key c hv).trans ((locallyDiscrete_ext h).trans (key c' hv).symm))
    (fun {v w} e => ?_) fun x hx => absurd hx (by have := U.grade_le_dimension x; omega)),
    fun x => ⟨(bicategoryNerve _).map (toAtomPoint U).op (nervePointCell ⟨⟨x⟩⟩), rfl⟩⟩
  have hv := (key c (grade_eq_zero_of_boundary_zero_eq_Iic e.2.2.1)).trans
    ((locallyDiscrete_ext h).trans (key c' (grade_eq_zero_of_boundary_zero_eq_Iic e.2.2.1)).symm)
  have hw := (key c (grade_eq_zero_of_boundary_zero_eq_Iic e.2.2.2)).trans
    ((locallyDiscrete_ext h).trans (key c' (grade_eq_zero_of_boundary_zero_eq_Iic e.2.2.2)).symm)
  have : Subsingleton (c.1.toPrefunctor.obj v ⟶ c.1.toPrefunctor.obj w) :=
    ⟨fun f g => by
      obtain ⟨⟨⟨f⟩⟩⟩ := f
      obtain ⟨⟨⟨g⟩⟩⟩ := g
      rfl⟩
  exact Subsingleton.helim (congrArg₂ (· ⟶ ·) hv hw) _ _

example :
    Nat.card (diagram (bicategoryNerve (LocallyDiscrete (Discrete Bool))) (atomGlobe 1)) = 2 := by
  rw [Nat.card_eq_of_bijective _ (bijective_obj_top_locallyDiscrete (dimension_atomGlobe 1)),
    Nat.card_eq_fintype_card, Fintype.card_bool]

end LocallyDiscrete

end Atoms.Diagrammatic
