import Atoms.Diagrammatic.BicategoryNerve.InftyTwo

open CategoryTheory Opposite Order Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape
open CategoryTheory.Bicategory (PathCell pathComp pathCompCompIso pathCell_id_ext pathCell_hom_eq
  pathCell_eqToHom eqToHom_eq_pathCompCompIso_assoc pathCell_comp_eqToHom pathCell_eqToHom_comp
  pathCell_whisker_eq)
open CategoryTheory.FreeBicategory (lift IsStructural eq_of_pathCell_eq_isStructural_left
  eq_of_pathCell_eq_isStructural_right)
open scoped CategoryTheory.Bicategory

universe w v u v'

namespace Atoms.Diagrammatic

variable {B : Type u} [Bicategory.{w, v} B]

namespace RoundBicat

variable {a b c d : RoundBicat (bicategoryNerve.{w, v, u} B) 0}

theorem dim_diag_le_two (a : RoundBicat (bicategoryNerve.{w, v, u} B) 0) : a.diag.dim ≤ 2 := by
  rw [a.dim_diag]; omega

noncomputable def nerveObj (a : RoundBicat (bicategoryNerve.{w, v, u} B) 0) : B :=
  (a.diag.nerveComposite a.dim_diag_le_two).src

theorem nerveComposite_src_tgt_of_mem {f : a ⟶ b} {x : PastingDiagram _} (hx : f.Mem x)
    (hd : x.dim ≤ 2) :
    (x.nerveComposite hd).src = nerveObj a ∧ (x.nerveComposite hd).tgt = nerveObj b := by
  have hb (α : Bool) : (x.boundary 0 α).dim ≤ 2 :=
    (x.shape.dimension_boundary_le 0 α).trans (Nat.zero_le 2)
  have e₀ := (PastingDiagram.nerveComposite_boundary_zero x hd false (hb false)).symm.trans
    (PastingDiagram.nerveComposite_congr hx.hasBdry.side (hb false) a.dim_diag_le_two)
  have e₁ := (PastingDiagram.nerveComposite_boundary_zero x hd true (hb true)).symm.trans
    (PastingDiagram.nerveComposite_congr hx.hasBdry.other (hb true) b.dim_diag_le_two)
  have h₀ := congrArg PathCell.src e₀
  have h₁ := congrArg PathCell.src e₁
  exact ⟨h₀, h₁⟩

theorem _root_.Atoms.Diagrammatic.RoundBicat.Hom.Mem.dim_le_two {f : a ⟶ b}
    {x : PastingDiagram (bicategoryNerve.{w, v, u} B)} (hx : f.Mem x) : x.dim ≤ 2 := by
  rw [hx.dim_eq]; omega

noncomputable def nervePath (f : a ⟶ b) : Quiver.Path (nerveObj a) (nerveObj b) :=
  ((f.rep.diag.nerveComposite f.mem_rep.dim_le_two).dom).cast
    (nerveComposite_src_tgt_of_mem f.mem_rep _).1 (nerveComposite_src_tgt_of_mem f.mem_rep _).2

theorem nerveComposite_of_mem {f : a ⟶ b} {x : PastingDiagram _} (hx : f.Mem x)
    (hd : x.dim ≤ 2) :
    x.nerveComposite hd = ⟨_, _, nervePath f, nervePath f, 𝟙 _⟩ := by
  have h1 : f.rep.diag.dim ≤ 1 := by rw [f.mem_rep.dim_eq]
  obtain ⟨p, hp⟩ := PastingDiagram.exists_nerveComposite_eq_of_dim_le_one
    f.rep.diag.toPastingDiagram f.mem_rep.dim_le_two h1
  refine (PastingDiagram.nerveComposite_congr (hx.equiv f.mem_rep) hd _).trans
    (hp.trans (pathCell_id_ext (nerveComposite_src_tgt_of_mem f.mem_rep _).1
      (nerveComposite_src_tgt_of_mem f.mem_rep _).2 ?_))
  exact (congr_arg_heq PathCell.dom hp).symm.trans (Quiver.Path.cast_heq _ _ _).symm

theorem exists_nerveComposite_eq {f g : a ⟶ b} (t : Cell f g) :
    ∃ φ, t.diag.nerveComposite t.dim_diag.le =
      ⟨nerveObj a, nerveObj b, nervePath f, nervePath g, φ⟩ := by
  have hb (α : Bool) : (t.diag.boundary 1 α).dim ≤ 2 :=
    (t.diag.shape.dimension_boundary_le 1 α).trans one_le_two
  have h₀ := (PastingDiagram.nerveComposite_boundary_one _ t.dim_diag.le false
    (hb false)).symm.trans
    (nerveComposite_of_mem t.source (hb false))
  have h₁ := (PastingDiagram.nerveComposite_boundary_one _ t.dim_diag.le true (hb true)).symm.trans
    (nerveComposite_of_mem t.target (hb true))
  obtain ⟨ha₀, hb₀, hP₀, -, -⟩ := PathCell.mk.inj h₀
  obtain ⟨-, -, hQ₁, -, -⟩ := PathCell.mk.inj h₁
  simp only [cond_false] at hP₀
  simp only [cond_true] at hQ₁
  exact PastingDiagram.pathCell_exists_eq_mk _ ha₀ hb₀ hP₀ hQ₁

noncomputable def cellComposite {f g : a ⟶ b} (t : Cell f g) :
    pathComp (𝟭q B) (nervePath f) ⟶ pathComp (𝟭q B) (nervePath g) :=
  (exists_nerveComposite_eq t).choose

theorem nerveComposite_eq_cellComposite {f g : a ⟶ b} (t : Cell f g) :
    t.diag.nerveComposite t.dim_diag.le =
      ⟨nerveObj a, nerveObj b, nervePath f, nervePath g, cellComposite t⟩ :=
  (exists_nerveComposite_eq t).choose_spec

theorem cellComposite_eq {f g : a ⟶ b} (t : Cell f g) {hd : t.diag.dim ≤ 2}
    {φ : pathComp (𝟭q B) (nervePath f) ⟶ pathComp (𝟭q B) (nervePath g)}
    (h : t.diag.nerveComposite hd = ⟨nerveObj a, nerveObj b, nervePath f, nervePath g, φ⟩) :
    cellComposite t = φ :=
  pathCell_hom_eq ((nerveComposite_eq_cellComposite t).symm.trans h)

theorem cellComposite_eq_of_equivalent {f g : a ⟶ b} {t t' : Cell f g}
    (h : Equivalent t.diag t'.diag) : cellComposite t = cellComposite t' :=
  (cellComposite_eq t' ((nerveComposite_eq_of_equivalent h (t.dim_diag.trans rfl) _
    t'.dim_diag.le).symm.trans (nerveComposite_eq_cellComposite t))).symm

noncomputable def nerveMap₂ {f g : a ⟶ b} (η : f ⟶ g) :
    pathComp (𝟭q B) (nervePath f) ⟶ pathComp (𝟭q B) (nervePath g) :=
  Quotient.lift (s := Cell.setoid f g) cellComposite (fun _ _ h => cellComposite_eq_of_equivalent h)
    η

theorem nerveMap₂_homMk {f g : a ⟶ b} (t : Cell f g) : nerveMap₂ (homMk t) = cellComposite t :=
  rfl

theorem nerveMap₂_id (f : a ⟶ b) : nerveMap₂ (𝟙 f) = 𝟙 _ :=
  cellComposite_eq (hd := (Cell.unitOf f.mem_rep f.mem_rep).dim_diag.le) _
    (PastingDiagram.nerveComposite_unit_of_dim_eq_one _ f.mem_rep.dim_eq
      (Cell.unitOf f.mem_rep f.mem_rep).dim_diag.le (nerveComposite_of_mem f.mem_rep _))

theorem nerveMap₂_comp {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    nerveMap₂ (η ≫ θ) = nerveMap₂ η ≫ nerveMap₂ θ := by
  induction η using Quotient.inductionOn with | h t => ?_
  induction θ using Quotient.inductionOn with | h s => ?_
  exact cellComposite_eq (t.comp s) (hd := (t.comp s).dim_diag.le)
    (PastingDiagram.nerveComposite_pasteAlong_one t.diag.toPastingDiagram
      s.diag.toPastingDiagram (t.pastable s).1.iso (t.pastable s).1.map_comm t.dim_diag.le
      s.dim_diag.le (t.comp s).dim_diag.le (nerveComposite_eq_cellComposite t)
      (nerveComposite_eq_cellComposite s))

theorem nervePath_id (a : RoundBicat (bicategoryNerve.{w, v, u} B) 0) :
    nervePath (𝟙 a) = (𝟙 (nerveObj a)).toPath := by
  obtain ⟨b, hb⟩ := PastingDiagram.exists_nerveComposite_eq_of_dim_eq_zero a.diag.toPastingDiagram
    a.dim_diag_le_two a.dim_diag
  have hu : a.diag.unit.dim ≤ 2 := by rw [PastingDiagram.dim_unit, a.dim_diag]; omega
  have e := (nerveComposite_of_mem (Hom.mem_id a) hu).symm.trans
    (PastingDiagram.nerveComposite_unit_of_dim_eq_zero _ a.dim_diag hu hb)
  obtain ⟨h₁, -, h₃, -, -⟩ := PathCell.mk.inj e
  have hab : nerveObj a = b := congrArg PathCell.src hb
  subst hab
  exact eq_of_heq h₃

theorem nervePath_comp (f : a ⟶ b) (g : b ⟶ c) :
    nervePath (f ≫ g) = (nervePath f).comp (nervePath g) := by
  have hp : f.rep.diag.Pastable g.rep.diag.toPastingDiagram 0 :=
    f.mem_rep.hasBdry.pastable g.mem_rep.hasBdry (.refl _)
  have hm := Hom.Mem.comp f.mem_rep g.mem_rep hp
  have e := (nerveComposite_of_mem hm hm.dim_le_two).symm.trans
    (PastingDiagram.nerveComposite_pasteAlong_zero f.rep.diag.toPastingDiagram
      g.rep.diag.toPastingDiagram hp.1.iso hp.1.map_comm f.mem_rep.dim_le_two
      g.mem_rep.dim_le_two hm.dim_le_two (nerveComposite_of_mem f.mem_rep _)
      (nerveComposite_of_mem g.mem_rep _))
  obtain ⟨-, -, h₃, -, -⟩ := PathCell.mk.inj e
  exact eq_of_heq h₃

noncomputable def nerveMapComp (f : a ⟶ b) (g : b ⟶ c) :
    pathComp (𝟭q B) (nervePath (f ≫ g)) ≅
      pathComp (𝟭q B) (nervePath f) ≫ pathComp (𝟭q B) (nervePath g) :=
  eqToIso (congrArg (pathComp (𝟭q B)) (nervePath_comp f g)) ≪≫ pathCompCompIso (𝟭q B) _ _

noncomputable def nerveMapId (a : RoundBicat (bicategoryNerve.{w, v, u} B) 0) :
    pathComp (𝟭q B) (nervePath (𝟙 a)) ≅ 𝟙 (nerveObj a) :=
  eqToIso (congrArg (pathComp (𝟭q B)) (nervePath_id a)) ≪≫ λ_ (𝟙 _)

theorem nerveMap₂_whiskerLeft (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    nerveMap₂ (f ◁ η) = (nerveMapComp f g).hom ≫ pathComp (𝟭q B) (nervePath f) ◁ nerveMap₂ η ≫
      (nerveMapComp f h).inv := by
  obtain ⟨t, rfl⟩ := homMk_surjective η
  rw [whiskerLeft_homMk_of_mem f.mem_rep t, nerveMap₂_homMk, nerveMap₂_homMk]
  have hd := (Cell.whiskerLeftOf f.mem_rep _ t.dim_diag t.source t.target).dim_diag.le
  refine cellComposite_eq _ (hd := hd) ((PastingDiagram.nerveComposite_rounding_paste_left _
    f.mem_rep.dim_eq t.dim_diag hd (nerveComposite_of_mem f.mem_rep _)
    (nerveComposite_eq_cellComposite t)).trans ?_)
  simp only [nerveMapComp, Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv, Category.assoc]
  have e := (pathCell_eqToHom (nervePath_comp f g) (nervePath_comp f h).symm
    ((pathCompCompIso (𝟭q B) _ _).hom ≫ pathComp (𝟭q B) (nervePath f) ◁ cellComposite t ≫
      (pathCompCompIso (𝟭q B) _ _).inv)).symm
  simp only [Category.assoc] at e
  exact e

theorem nerveMap₂_whiskerRight {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    nerveMap₂ (η ▷ h) = (nerveMapComp f h).hom ≫ nerveMap₂ η ▷ pathComp (𝟭q B) (nervePath h) ≫
      (nerveMapComp g h).inv := by
  obtain ⟨t, rfl⟩ := homMk_surjective η
  rw [homMk_whiskerRight_of_mem h.mem_rep t, nerveMap₂_homMk, nerveMap₂_homMk]
  have hd := (Cell.whiskerRightOf _ t.dim_diag t.source t.target h.mem_rep).dim_diag.le
  refine cellComposite_eq _ (hd := hd) ((PastingDiagram.nerveComposite_rounding_paste_right _
    t.dim_diag h.mem_rep.dim_eq hd (nerveComposite_eq_cellComposite t)
    (nerveComposite_of_mem h.mem_rep _)).trans ?_)
  simp only [nerveMapComp, Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv, Category.assoc]
  have e := (pathCell_eqToHom (nervePath_comp f h) (nervePath_comp g h).symm
    ((pathCompCompIso (𝟭q B) _ _).hom ≫ cellComposite t ▷ pathComp (𝟭q B) (nervePath h) ≫
      (pathCompCompIso (𝟭q B) _ _).inv)).symm
  simp only [Category.assoc] at e
  exact e

theorem nerveMap₂_eqToHom {f g : a ⟶ b} (h : f = g) :
    nerveMap₂ (eqToHom h) = eqToHom (congrArg (fun k => pathComp (𝟭q B) (nervePath k)) h) := by
  subst h
  exact nerveMap₂_id f

theorem nerveMap₂_associator (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    nerveMap₂ (α_ f g h).hom = (nerveMapComp (f ≫ g) h).hom ≫
      (nerveMapComp f g).hom ▷ pathComp (𝟭q B) (nervePath h) ≫ (α_ _ _ _).hom ≫
      pathComp (𝟭q B) (nervePath f) ◁ (nerveMapComp g h).inv ≫ (nerveMapComp f (g ≫ h)).inv := by
  rw [associator_hom, nerveMap₂_eqToHom]
  simp only [nerveMapComp, Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv]
  exact eqToHom_eq_pathCompCompIso_assoc (nervePath f) (nervePath g) (nervePath h)
    (nervePath_comp f g) (nervePath_comp g h) (nervePath_comp (f ≫ g) h) (nervePath_comp f (g ≫ h))
    (congrArg nervePath (assoc f g h))

noncomputable def ofBoundary (m : PastingDiagram (bicategoryNerve.{w, v, u} B)) (hm : m.dim = 1)
    (hr : m.IsRound) (β : Bool) : RoundBicat (bicategoryNerve.{w, v, u} B) 0 :=
  ⟨⟨m.boundary 0 β, PastingDiagram.isRound_boundary_of_isRound hr 0 β⟩,
    PastingDiagram.dim_boundary m (by omega) β⟩

noncomputable def homOfDimOne (m : PastingDiagram (bicategoryNerve.{w, v, u} B)) (hm : m.dim = 1)
    (hr : m.IsRound) : ofBoundary m hm hr false ⟶ ofBoundary m hm hr true :=
  Arrow.hom ⟨⟨m, hr⟩, ⟨hm, PastingDiagram.dim_boundary m (by omega) false,
    PastingDiagram.dim_boundary m (by omega) true, .refl _, .refl _⟩⟩

theorem nerveComposite_cylDiagram_left (m : PastingDiagram (bicategoryNerve.{w, v, u} B))
    (hm : m.dim = 1) (hr : m.IsRound)
    (hd : (PastingDiagram.cylDiagram m (m.shape.ogp.boundary ⊤ 0 true)).dim ≤ 2) :
    ∃ (x y : B) (P : Quiver.Path x y)
      (θ : pathComp (𝟭q B) P ⟶ pathComp (𝟭q B) ((𝟙 x).toPath.comp P)),
      (PastingDiagram.cylDiagram m (m.shape.ogp.boundary ⊤ 0 true)).nerveComposite hd =
        ⟨x, y, P, (𝟙 x).toPath.comp P, θ⟩ := by
  have hf : (homOfDimOne m hm hr).Mem m := (Arrow.mem_hom _ _).2 (.refl _)
  generalize homOfDimOne m hm hr = f at hf
  have hfit : (unitorSpec false (ofBoundary m hm hr false) (ofBoundary m hm hr true)).Fits
      f.rep.diag.toPastingDiagram :=
    ⟨f.rep.diag.isRound, by rw [f.mem_rep.dim_eq]; exact Nat.lt_succ_self 0, f.mem_rep.hasBdry.side⟩
  have e := CylSpec.fam_equiv hfit (f.mem_rep.equiv hf)
  rw [CylSpec.fam_def m, PastingDiagram.cylDiagram_congr m (unitorSpec_K false hf),
    ← Cell.leftUnitor_diag] at e
  have hQ := (nervePath_comp (𝟙 (ofBoundary m hm hr false)) f).trans
    (congrArg (fun p => Quiver.Path.comp p (nervePath f)) (nervePath_id _))
  exact ⟨_, _, _, _, (PastingDiagram.nerveComposite_congr e.symm hd
    (Cell.leftUnitor f).dim_diag.le).trans
      ((nerveComposite_eq_cellComposite (Cell.leftUnitor f)).trans
      (pathCell_comp_eqToHom hQ _))⟩

theorem nerveComposite_cylDiagram_right (m : PastingDiagram (bicategoryNerve.{w, v, u} B))
    (hm : m.dim = 1) (hr : m.IsRound)
    (hd : (PastingDiagram.cylDiagram m (m.shape.ogp.boundary ⊤ 0 false)).dim ≤ 2) :
    ∃ (x y : B) (P : Quiver.Path x y)
      (θ : pathComp (𝟭q B) (P.comp (𝟙 y).toPath) ⟶ pathComp (𝟭q B) P),
      (PastingDiagram.cylDiagram m (m.shape.ogp.boundary ⊤ 0 false)).nerveComposite hd =
        ⟨x, y, P.comp (𝟙 y).toPath, P, θ⟩ := by
  have hf : (homOfDimOne m hm hr).Mem m := (Arrow.mem_hom _ _).2 (.refl _)
  generalize homOfDimOne m hm hr = f at hf
  have hfit : (unitorSpec true (ofBoundary m hm hr false) (ofBoundary m hm hr true)).Fits
      f.rep.diag.toPastingDiagram :=
    ⟨f.rep.diag.isRound, by rw [f.mem_rep.dim_eq]; exact Nat.lt_succ_self 0,
      f.mem_rep.hasBdry.other⟩
  have e := CylSpec.fam_equiv hfit (f.mem_rep.equiv hf)
  rw [CylSpec.fam_def m, PastingDiagram.cylDiagram_congr m (unitorSpec_K true hf),
    ← Cell.rightUnitor_diag] at e
  have hP := (nervePath_comp f (𝟙 (ofBoundary m hm hr true))).trans
    (congrArg (fun p => Quiver.Path.comp (nervePath f) p) (nervePath_id _))
  exact ⟨_, _, _, _, (PastingDiagram.nerveComposite_congr e.symm hd
    (Cell.rightUnitor f).dim_diag.le).trans ((nerveComposite_eq_cellComposite
      (Cell.rightUnitor f)).trans (pathCell_eqToHom_comp hP _))⟩

theorem exists_tautLabelling (M : MoleculeShape) (hM : M.dimension ≤ 1) :
    ∃ φ : realize.obj M.rdc ⟶
        bicategoryNerve.{_, _, 0} (FreeBicategory (EdgeQuiver M.rdc.obj.toOGP)),
      ∀ ℓ : Labelling B M.rdc.obj.toOGP M.rdc.obj.isRDC,
        (bicategoryNerveHomEquiv _ M.rdc φ).1.toPrefunctor ⋙q (lift ℓ.toPrefunctor).toPrefunctor =
          ℓ.toPrefunctor :=
  ⟨(bicategoryNerveHomEquiv _ M.rdc).symm ⟨Labelling.free fun x hx => by
      have := grade_le_of_dimension_le M hM x; omega, fun y hy => absurd hy (by
      have := grade_le_of_dimension_le M hM y; omega)⟩,
    fun ℓ => by
      rw [Equiv.apply_symm_apply]
      exact Labelling.free_comp_lift _ _ ℓ.obj_eq_of_boundary_Iic⟩

theorem nerveMap₂_leftUnitor_inv (f : a ⟶ b) :
    nerveMap₂ (λ_ f).inv = (λ_ (pathComp (𝟭q B) (nervePath f))).inv ≫
      (nerveMapId a).inv ▷ pathComp (𝟭q B) (nervePath f) ≫ (nerveMapComp (𝟙 a) f).inv := by
  have hM : f.rep.diag.shape.dimension ≤ 1 := f.mem_rep.dim_eq.le
  have e : (Cell.leftUnitor f).diag.toPastingDiagram = PastingDiagram.cylDiagram
      f.rep.diag.toPastingDiagram (f.rep.diag.shape.ogp.boundary ⊤ 0 true) :=
    (Cell.leftUnitor_diag f).trans ((CylSpec.fam_def _).trans
      (PastingDiagram.cylDiagram_congr _ (unitorSpec_K false f.mem_rep)))
  have hd : (PastingDiagram.cylDiagram f.rep.diag.toPastingDiagram
      (f.rep.diag.shape.ogp.boundary ⊤ 0 true)).dim ≤ 2 := e ▸ (Cell.leftUnitor f).dim_diag.le
  have hB := (PastingDiagram.nerveComposite_congr (PastingDiagram.equiv_of_eq e.symm) hd
    (Cell.leftUnitor f).dim_diag.le).trans (nerveComposite_eq_cellComposite (Cell.leftUnitor f))
  obtain ⟨φ', hφ'⟩ := exists_tautLabelling (B := B) f.rep.diag.shape hM
  obtain ⟨x', y', P', θ, hF⟩ := nerveComposite_cylDiagram_left ⟨f.rep.diag.shape, φ'⟩
    f.mem_rep.dim_eq f.rep.diag.isRound hd
  obtain ⟨ψ, hψ, he⟩ := PastingDiagram.nerveComposite_of_freeImage
    (bicategoryNerveHomEquiv B _ f.rep.diag.map).1.toPrefunctor _ f.rep.diag.map φ'
    (hφ' _).symm hM hd hF
  simp only [nerveMapId, nerveMapComp, Iso.trans_inv, eqToIso.inv]
  exact eq_of_pathCell_eq_isStructural_left _ (nervePath_id a) (nervePath_comp (𝟙 a) f) hψ
    (hB.symm.trans he)

theorem nerveMap₂_rightUnitor_hom (f : a ⟶ b) :
    nerveMap₂ (ρ_ f).hom = (nerveMapComp f (𝟙 b)).hom ≫
      pathComp (𝟭q B) (nervePath f) ◁ (nerveMapId b).hom ≫
        (ρ_ (pathComp (𝟭q B) (nervePath f))).hom := by
  have hM : f.rep.diag.shape.dimension ≤ 1 := f.mem_rep.dim_eq.le
  have e : (Cell.rightUnitor f).diag.toPastingDiagram = PastingDiagram.cylDiagram
      f.rep.diag.toPastingDiagram (f.rep.diag.shape.ogp.boundary ⊤ 0 false) :=
    (Cell.rightUnitor_diag f).trans ((CylSpec.fam_def _).trans
      (PastingDiagram.cylDiagram_congr _ (unitorSpec_K true f.mem_rep)))
  have hd : (PastingDiagram.cylDiagram f.rep.diag.toPastingDiagram
      (f.rep.diag.shape.ogp.boundary ⊤ 0 false)).dim ≤ 2 := e ▸ (Cell.rightUnitor f).dim_diag.le
  have hB := (PastingDiagram.nerveComposite_congr (PastingDiagram.equiv_of_eq e.symm) hd
    (Cell.rightUnitor f).dim_diag.le).trans (nerveComposite_eq_cellComposite (Cell.rightUnitor f))
  obtain ⟨φ', hφ'⟩ := exists_tautLabelling (B := B) f.rep.diag.shape hM
  obtain ⟨x', y', P', θ, hF⟩ := nerveComposite_cylDiagram_right ⟨f.rep.diag.shape, φ'⟩
    f.mem_rep.dim_eq f.rep.diag.isRound hd
  obtain ⟨ψ, hψ, he⟩ := PastingDiagram.nerveComposite_of_freeImage
    (bicategoryNerveHomEquiv B _ f.rep.diag.map).1.toPrefunctor _ f.rep.diag.map φ'
    (hφ' _).symm hM hd hF
  simp only [nerveMapId, nerveMapComp, Iso.trans_hom, eqToIso.hom]
  exact eq_of_pathCell_eq_isStructural_right _ (nervePath_id b) (nervePath_comp f (𝟙 b)) hψ
    (hB.symm.trans he)

theorem nerveMap₂_leftUnitor_hom (f : a ⟶ b) :
    nerveMap₂ (λ_ f).hom = (nerveMapComp (𝟙 a) f).hom ≫
      (nerveMapId a).hom ▷ pathComp (𝟭q B) (nervePath f) ≫
        (λ_ (pathComp (𝟭q B) (nervePath f))).hom := by
  have hl : nerveMap₂ (λ_ f).hom ≫ nerveMap₂ (λ_ f).inv = 𝟙 _ := by
    rw [← nerveMap₂_comp, Iso.hom_inv_id, nerveMap₂_id]
  exact (Iso.comp_inv_eq_id (nerveMapComp (𝟙 a) f ≪≫
    Bicategory.whiskerRightIso (nerveMapId a) _ ≪≫ λ_ _)).1 ((congrArg (_ ≫ ·)
      ((nerveMap₂_leftUnitor_inv f).trans (Category.assoc _ _ _).symm)).symm.trans hl)

theorem pathCell_nerveMap₂_conj_whisker {f f' g g' : a ⟶ b} (hf : f' = 𝟙 a ≫ f)
    (hg : g' = 𝟙 a ≫ g) (η : f ⟶ g) :
    (⟨_, _, nervePath f', nervePath g', nerveMap₂ (eqToHom hf ≫ 𝟙 a ◁ η ≫ eqToHom hg.symm)⟩ :
        PathCell B) =
      ⟨_, _, (nervePath (𝟙 a)).comp (nervePath f), (nervePath (𝟙 a)).comp (nervePath g),
        (pathCompCompIso (𝟭q B) _ _).hom ≫ pathComp (𝟭q B) (nervePath (𝟙 a)) ◁ nerveMap₂ η ≫
          (pathCompCompIso (𝟭q B) _ _).inv⟩ := by
  subst hf hg
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [nerveMap₂_whiskerLeft]
  simp only [nerveMapComp, Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv, Category.assoc]
  have e := pathCell_eqToHom (nervePath_comp (𝟙 a) f) (nervePath_comp (𝟙 a) g).symm
    ((pathCompCompIso (𝟭q B) _ _).hom ≫ pathComp (𝟭q B) (nervePath (𝟙 a)) ◁ nerveMap₂ η ≫
      (pathCompCompIso (𝟭q B) _ _).inv)
  simp only [Category.assoc] at e
  exact e

end RoundBicat

variable (B) in
noncomputable def nerveCompositeFunctor : RoundBicat (bicategoryNerve.{w, v, u} B) 0 ⥤ᵖ B where
  obj := RoundBicat.nerveObj
  map f := pathComp (𝟭q B) (RoundBicat.nervePath f)
  map₂ := RoundBicat.nerveMap₂
  map₂_id := RoundBicat.nerveMap₂_id
  map₂_comp := RoundBicat.nerveMap₂_comp
  mapId := RoundBicat.nerveMapId
  mapComp := RoundBicat.nerveMapComp
  map₂_whisker_left := RoundBicat.nerveMap₂_whiskerLeft
  map₂_whisker_right := RoundBicat.nerveMap₂_whiskerRight
  map₂_associator := RoundBicat.nerveMap₂_associator
  map₂_left_unitor := RoundBicat.nerveMap₂_leftUnitor_hom
  map₂_right_unitor := RoundBicat.nerveMap₂_rightUnitor_hom

variable {a b : RoundBicat (bicategoryNerve.{w, v, u} B) 0}

theorem nerveCompositeFunctor_map₂_homMk {f g : a ⟶ b} (t : RoundBicat.Cell f g) :
    t.diag.nerveComposite t.dim_diag.le =
      ⟨_, _, RoundBicat.nervePath f, RoundBicat.nervePath g,
        (nerveCompositeFunctor B).map₂ (RoundBicat.homMk t)⟩ :=
  RoundBicat.nerveComposite_eq_cellComposite t

namespace Layered.Signature.Interp

variable {S : Signature.{v'}} [DecidableEq S.Pt] [DecidableEq S.Ed] (hS : S.WellFormed)
  (I : S.Interp (bicategoryNerve.{w, v, u} B))

theorem nerveComposite_roundDiagram (d : Diagram S.Pt S.Ed S.Ce) {x y : S.Pt}
    (hx : S.pathEnds d.source = some (x, y)) {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q)
    (hd : (I.roundDiagram hS hq (S.isPath_of_pathEnds hx).ne_nil).dim ≤ 2) :
    (I.roundDiagram hS hq (S.isPath_of_pathEnds hx).ne_nil).nerveComposite hd =
      PathCell.ofHom (I.reading hS).label (S.toPath d.source (S.walk_of_pathEnds hx))
        (S.toPath q (S.walk_of_pathEnds (S.pathEnds_target hS hq hx)))
        ((I.reading hS).evalB d hx hq) := by
  have hsrc := (S.isPath_of_pathEnds hx).ne_nil
  have hdd := I.dim_diagram hS hq hsrc
  obtain ⟨p, _ | ⟨l, ls⟩⟩ := d
  · have e : (I.roundDiagram hS hq hsrc).toPastingDiagram = I.diagram ⟨p, []⟩ hsrc :=
      (I.diagram_unit_singleton hsrc).trans (I.diagram_nil hsrc).symm
    exact (PastingDiagram.nerveComposite_congr (PastingDiagram.equiv_of_eq e) hd hdd.le).trans
      (I.nerveComposite_diagram hS hx hq hsrc hdd.le)
  · obtain ⟨hp, e⟩ := I.exists_equiv_roundDiagram hS hq hsrc (List.cons_ne_nil _ _)
    have hpd : ((I.path p hsrc).unit.paste (I.diagram ⟨p, l :: ls⟩ hsrc) 1 hp).dim ≤ 2 :=
      (PastingDiagram.dim_eq_of_equiv e) ▸ hd
    exact (PastingDiagram.nerveComposite_congr e hd hpd).trans
      (PastingDiagram.nerveComposite_unit_paste (I.dim_path (S.isPath_of_pathEnds hx)) hdd hp hpd
        (I.nerveComposite_diagram hS hx hq hsrc hdd.le))

theorem nerveCompositeFunctor_map₂_roundCell (d : Diagram S.Pt S.Ed S.Ce) {x y : S.Pt}
    (hx : S.pathEnds d.source = some (x, y)) {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) :
    (⟨_, _, RoundBicat.nervePath _, RoundBicat.nervePath _,
        (nerveCompositeFunctor B).map₂ (RoundBicat.homMk (I.roundCell hS d hx hq))⟩ : PathCell B) =
      PathCell.ofHom (I.reading hS).label (S.toPath d.source (S.walk_of_pathEnds hx))
        (S.toPath q (S.walk_of_pathEnds (S.pathEnds_target hS hq hx)))
        ((I.reading hS).evalB d hx hq) :=
  (nerveCompositeFunctor_map₂_homMk _).symm.trans (I.nerveComposite_roundDiagram hS d hx hq _)

theorem nerveCompositeFunctor_map₂_evalB (d : Diagram S.Pt S.Ed S.Ce) {x y : S.Pt}
    (hx : S.pathEnds d.source = some (x, y)) {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) :
    (⟨_, _, RoundBicat.nervePath _, RoundBicat.nervePath _,
        (nerveCompositeFunctor B).map₂ ((I.toRoundBicat hS).evalB d hx hq)⟩ : PathCell B) =
      ⟨_, _, (𝟙 ((I.reading hS).label.obj x)).toPath.comp
          ((I.reading hS).label.mapPath (S.toPath d.source (S.walk_of_pathEnds hx))),
        (𝟙 ((I.reading hS).label.obj x)).toPath.comp ((I.reading hS).label.mapPath
          (S.toPath q (S.walk_of_pathEnds (S.pathEnds_target hS hq hx)))),
        (pathCompCompIso (𝟭q B) _ _).hom ≫
          pathComp (𝟭q B) (𝟙 ((I.reading hS).label.obj x)).toPath ◁
            (PathCell.ofHom (I.reading hS).label (S.toPath d.source (S.walk_of_pathEnds hx))
              (S.toPath q (S.walk_of_pathEnds (S.pathEnds_target hS hq hx)))
              ((I.reading hS).evalB d hx hq)).hom ≫
          (pathCompCompIso (𝟭q B) _ _).inv⟩ := by
  have hc := I.nerveCompositeFunctor_map₂_roundCell hS d hx hq
  obtain ⟨hobj, -, -, -, -⟩ := PathCell.mk.inj hc
  rw [I.evalB_toRoundBicat hS d hx hq]
  refine (RoundBicat.pathCell_nerveMap₂_conj_whisker (I.pathComp_toPath _ hx)
    (I.pathComp_toPath _ (S.pathEnds_target hS hq hx))
    (RoundBicat.homMk (I.roundCell hS d hx hq))).trans (pathCell_whisker_eq ?_ hc)
  rw [RoundBicat.nervePath_id]
  exact PastingDiagram.toPath_heq hobj hobj (congr_arg_heq (𝟙 ·) hobj)

end Layered.Signature.Interp

namespace Layered

variable {S : RelSignature.{v'}} [DecidableEq S.Pt] [DecidableEq S.Ed] {hS : S.WellFormed}

theorem RelSignature.RewriteChain.evalB_eq [DecidableEq S.Ce]
    (F : S.toSignature.BicatInterp hS.1 B) (hF : F.Satisfies hS) {d d' : Diagram S.Pt S.Ed S.Ce}
    (p : S.RewriteChain d d') {x y x' y' : S.Pt} (hx : S.pathEnds d.source = some (x, y))
    (hx' : S.pathEnds d'.source = some (x', y')) {q q' : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hq' : S.target d' = some q') :
    PathCell.ofHom F.label (S.toPath d.source (S.walk_of_pathEnds hx))
        (S.toPath q (S.walk_of_pathEnds (S.pathEnds_target hS.1 hq hx))) (F.evalB d hx hq) =
      PathCell.ofHom F.label (S.toPath d'.source (S.walk_of_pathEnds hx'))
        (S.toPath q' (S.walk_of_pathEnds (S.pathEnds_target hS.1 hq' hx')))
        (F.evalB d' hx' hq') := by
  have hE := p.equivalent_roundDiagram (F.toNerve hF)
    ((F.toNerve hF).isEquivalence_rel_of_isInftyCategory isInftyCategory_bicategoryNerve le_rfl) hq
    (S.isPath_of_pathEnds hx).ne_nil hq' (S.isPath_of_pathEnds hx').ne_nil
  have h := ((F.toNerve hF).toInterp.nerveCompositeFunctor_map₂_roundCell hS.1 d hx hq).symm.trans
    ((nerveCompositeFunctor_map₂_homMk _).symm.trans ((nerveComposite_eq_of_equivalent hE
      ((F.toNerve hF).toInterp.roundCell hS.1 d hx hq).dim_diag _ _).trans
        ((nerveCompositeFunctor_map₂_homMk
          ((F.toNerve hF).toInterp.roundCell hS.1 d' hx' hq')).trans
          ((F.toNerve hF).toInterp.nerveCompositeFunctor_map₂_roundCell hS.1 d' hx' hq'))))
  rw [F.reading_toNerve hF] at h
  exact h

end Layered

end Atoms.Diagrammatic
