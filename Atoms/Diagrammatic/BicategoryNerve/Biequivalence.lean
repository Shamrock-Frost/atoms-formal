import Atoms.Diagrammatic.BicategoryNerve.RoundBicategory
import Atoms.ForMathlib.CategoryTheory.Bicategory.Biequivalence

open CategoryTheory Atoms.Shape
open CategoryTheory.Bicategory (PathCell pathComp)
open scoped CategoryTheory.Bicategory

universe w v u

namespace Atoms.Diagrammatic

theorem HasRoundType.hasBdry {X : DiagSet.{u}} {x : PastingDiagram X}
    {p q : RoundPastingDiagram X} (hx : HasRoundType x p q) :
    HasBdry false p.dim x p.toPastingDiagram q.toPastingDiagram :=
  ⟨hx.dim_eq, rfl, hx.dim_eq_dim.symm, hx.source, hx.target⟩

variable {B : Type u} [Bicategory.{w, v} B]

namespace RoundBicat

variable {a b : RoundBicat (bicategoryNerve.{w, v, u} B) 0}

def ofPoint (x : B) : RoundBicat (bicategoryNerve.{w, v, u} B) 0 :=
  ⟨cellRound (nervePointCell.{w, v, u} x), dimension_atomPoint⟩

theorem nerveObj_ofPoint (x : B) : nerveObj (ofPoint.{w, v, u} x) = x :=
  congrArg PathCell.src (PastingDiagram.nerveComposite_nervePointCell x _)

theorem exists_nervePath_eq_toPath (g : nerveObj a ⟶ nerveObj b) :
    ∃ f : a ⟶ b, nervePath f = g.toPath := by
  have hpar : Parallel a.diag b.diag := ⟨a.dim_diag.trans b.dim_diag.symm, .inl a.dim_diag⟩
  obtain ⟨c, hc⟩ := PastingDiagram.exists_nerveComposite_eq_of_dim_eq_zero a.diag.toPastingDiagram
    a.dim_diag_le_two a.dim_diag
  obtain ⟨d, hd⟩ := PastingDiagram.exists_nerveComposite_eq_of_dim_eq_zero b.diag.toPastingDiagram
    b.dim_diag_le_two b.dim_diag
  have hac : nerveObj a = c := congrArg PathCell.src hc
  have hbd : nerveObj b = d := congrArg PathCell.src hd
  subst hac hbd
  obtain ⟨x, hx, hxc⟩ := hpar.exists_nerveFiller_zero a.dim_diag a.dim_diag_le_two
    b.dim_diag_le_two hc hd g
  have hb : HasBdry false 0 (PastingDiagram.ofCell x) a.diag.toPastingDiagram
      b.diag.toPastingDiagram := by
    have h := hx.hasBdry
    rwa [a.dim_diag] at h
  let p : Arrow a b := ⟨cellRound x, hb⟩
  have hd₂ : (PastingDiagram.ofCell x).dim ≤ 2 := by rw [hb.dim_h]; omega
  have e := (nerveComposite_of_mem ((Arrow.mem_hom p _).2 (.refl _)) hd₂).symm.trans (hxc hd₂)
  obtain ⟨-, -, hP, -, -⟩ := PathCell.mk.inj e
  exact ⟨p.hom, eq_of_heq hP⟩

theorem exists_cellComposite_eq {f g : a ⟶ b}
    (φ : pathComp (𝟭q B) (nervePath f) ⟶ pathComp (𝟭q B) (nervePath g)) :
    ∃ t : Cell f g, cellComposite t = φ := by
  have hf := f.mem_rep.hasBdry
  have hg := g.mem_rep.hasBdry
  have hpar : Parallel f.rep.diag g.rep.diag := by
    refine ⟨f.mem_rep.dim_eq.trans g.mem_rep.dim_eq.symm, .inr fun α => ?_⟩
    rw [PastingDiagram.boundary_congr _ (show f.rep.diag.dim - 1 = 0 by rw [f.mem_rep.dim_eq]),
      PastingDiagram.boundary_congr _ (show g.rep.diag.dim - 1 = 0 by rw [g.mem_rep.dim_eq])]
    cases α
    · exact hf.side.trans hg.side.symm
    · exact hf.other.trans hg.other.symm
  obtain ⟨x, hx, hxc⟩ := hpar.exists_nerveFiller_one f.mem_rep.dim_eq f.mem_rep.dim_le_two
    g.mem_rep.dim_le_two (nerveComposite_of_mem f.mem_rep _) (nerveComposite_of_mem g.mem_rep _) φ
  let t : Cell f g :=
    { diag := cellRound x
      dim_diag := hx.dim_eq.trans (congrArg (· + 1) f.mem_rep.dim_eq)
      source := f.mem_rep.of_equiv (hx.equiv_boundary_cond f.mem_rep.dim_eq false).symm
      target := g.mem_rep.of_equiv (hx.equiv_boundary_cond f.mem_rep.dim_eq true).symm }
  exact ⟨t, cellComposite_eq t (hxc t.dim_diag.le)⟩

theorem equivalent_of_cellComposite_eq {f g : a ⟶ b} {t t' : Cell f g}
    (h : cellComposite t = cellComposite t') : Equivalent t.diag t'.diag := by
  have hpar : Parallel t.diag t'.diag := by
    refine ⟨t.dim_diag.trans t'.dim_diag.symm, .inr fun α => ?_⟩
    rw [PastingDiagram.boundary_congr _ (show t.diag.dim - 1 = 0 + 1 by rw [t.dim_diag]),
      PastingDiagram.boundary_congr _ (show t'.diag.dim - 1 = 0 + 1 by rw [t'.dim_diag])]
    cases α
    · exact t.source.equiv t'.source
    · exact t.target.equiv t'.target
  obtain ⟨x, hx⟩ := (hpar.exists_nerveFiller_two_iff t.dim_diag t.dim_diag.le
    t'.dim_diag.le).2 (by rw [nerveComposite_eq_cellComposite t,
      nerveComposite_eq_cellComposite t', h])
  refine Equivalent.of_hasRoundType hx (bicategoryNerve_mem_equivalences_of_three_le _ ?_)
  have h₃ := hx.dim_eq
  rw [t.dim_diag] at h₃
  exact h₃.ge

end RoundBicat

open RoundBicat

variable {a b : RoundBicat (bicategoryNerve.{w, v, u} B) 0}

theorem nerveCompositeFunctor_map₂_bijective {f g : a ⟶ b} :
    Function.Bijective ((nerveCompositeFunctor B).map₂ : (f ⟶ g) → _) := by
  refine ⟨fun η η' h => ?_, fun φ => ?_⟩
  · obtain ⟨t, rfl⟩ := homMk_surjective η
    obtain ⟨t', rfl⟩ := homMk_surjective η'
    have e : cellComposite t = cellComposite t' :=
      (nerveMap₂_homMk t).symm.trans (h.trans (nerveMap₂_homMk t'))
    exact (homMk_eq_homMk_iff t t').2 (equivalent_of_cellComposite_eq e)
  · obtain ⟨t, ht⟩ := exists_cellComposite_eq (f := f) (g := g) φ
    exact ⟨homMk t, ht⟩

theorem nerveCompositeFunctor_essFull
    (g : (nerveCompositeFunctor B).obj a ⟶ (nerveCompositeFunctor B).obj b) :
    ∃ f : a ⟶ b, Nonempty ((nerveCompositeFunctor B).map f ≅ g) := by
  obtain ⟨f, hf⟩ := exists_nervePath_eq_toPath g
  exact ⟨f, ⟨eqToIso (congrArg (pathComp (𝟭q B)) hf) ≪≫ λ_ g⟩⟩

theorem nerveCompositeFunctor_obj_surjective :
    Function.Surjective (nerveCompositeFunctor B).obj :=
  fun x => ⟨ofPoint x, nerveObj_ofPoint x⟩

instance (a b : RoundBicat (bicategoryNerve.{w, v, u} B) 0) :
    ((nerveCompositeFunctor B).mapFunctor a b).IsEquivalence where
  faithful := ⟨fun {f g} => (nerveCompositeFunctor_map₂_bijective (f := f) (g := g)).1⟩
  full := ⟨fun {f g} => (nerveCompositeFunctor_map₂_bijective (f := f) (g := g)).2⟩
  essSurj := ⟨fun g => nerveCompositeFunctor_essFull g⟩

private theorem isIso_of_pathCell_eq {x y x' y' : B} {P Q : Quiver.Path x y}
    {P' Q' : Quiver.Path x' y'} {φ : pathComp (𝟭q B) P ⟶ pathComp (𝟭q B) Q}
    {ψ : pathComp (𝟭q B) P' ⟶ pathComp (𝟭q B) Q'}
    (h : (⟨x, y, P, Q, φ⟩ : PathCell B) = ⟨x', y', P', Q', ψ⟩) [IsIso ψ] : IsIso φ := by
  cases h
  infer_instance

theorem isIso_of_bicategoryNerve_mem_equivalences
    (e : RoundPastingDiagram (bicategoryNerve.{w, v, u} B)) (he : e.dim = 2) {x y : B}
    {P Q : Quiver.Path x y} {φ : pathComp (𝟭q B) P ⟶ pathComp (𝟭q B) Q}
    (hφ : e.nerveComposite he.le = ⟨x, y, P, Q, φ⟩)
    (hm : e ∈ equivalences (bicategoryNerve.{w, v, u} B)) : IsIso φ := by
  have hb (α : Bool) : (e.boundary 1 α).dim = 1 := PastingDiagram.dim_boundary _ (by omega) α
  have hr (α : Bool) := PastingDiagram.isRound_boundary_of_isRound e.isRound 1 α
  have hg (α β : Bool) : ((e.boundary 1 α).boundary 0 β).Equiv (e.boundary 0 β) :=
    PastingDiagram.equiv_boundary_boundary _ one_pos α β
  let g : Arrow (ofBoundary _ (hb false) (hr false) false)
      (ofBoundary _ (hb false) (hr false) true) :=
    ⟨⟨_, hr true⟩, ⟨hb true, PastingDiagram.dim_boundary _ (by omega) false,
      PastingDiagram.dim_boundary _ (by omega) true, (hg true false).trans (hg false false).symm,
      (hg true true).trans (hg false true).symm⟩⟩
  let t : Cell (homOfDimOne _ (hb false) (hr false)) g.hom :=
    ⟨e, he, (Arrow.mem_hom _ _).2 (.refl _), (Arrow.mem_hom _ _).2 (.refl _)⟩
  have := (isIso_homMk_iff t).2 hm
  have : IsIso (cellComposite t) :=
    PrelaxFunctor.map₂_isIso (nerveCompositeFunctor B).toPrelaxFunctor (homMk t)
  exact isIso_of_pathCell_eq (hφ.symm.trans (nerveComposite_eq_cellComposite t))

variable (B) in
noncomputable def nervePseudoInverse : B ⥤ᵖ RoundBicat (bicategoryNerve.{w, v, u} B) 0 :=
  (nerveCompositeFunctor B).pseudoInverse ofPoint fun x =>
    Bicategory.Equivalence.ofEq (nerveObj_ofPoint x)

theorem nervePseudoInverse_obj (x : B) : (nervePseudoInverse B).obj x = RoundBicat.ofPoint x :=
  rfl

open CategoryTheory.Pseudofunctor.StrongTrans in
variable (B) in
noncomputable def nervePseudoInverseCounit :
    Bicategory.Equivalence ((nervePseudoInverse B).comp (nerveCompositeFunctor B))
      (Pseudofunctor.id B) :=
  Pseudofunctor.pseudoInverseCounit _ _ _

open CategoryTheory.Pseudofunctor.StrongTrans in
variable (B) in
noncomputable def nervePseudoInverseUnit :
    Bicategory.Equivalence (Pseudofunctor.id (RoundBicat (bicategoryNerve.{w, v, u} B) 0))
      ((nerveCompositeFunctor B).comp (nervePseudoInverse B)) :=
  Pseudofunctor.pseudoInverseUnit _ _ _

end Atoms.Diagrammatic
