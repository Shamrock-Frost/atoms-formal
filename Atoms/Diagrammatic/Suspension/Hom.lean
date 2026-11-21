import Atoms.Diagrammatic.Context.RoundBicategory
import Atoms.Diagrammatic.Core
import Atoms.Diagrammatic.HomotopyCategory
import Atoms.Diagrammatic.Localization.MappingPathSpace
import Atoms.Diagrammatic.MappingSpace
import Atoms.Diagrammatic.Suspension.Realization
import Atoms.ForMathlib.CategoryTheory.LiftingProperties.Over
import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

open CategoryTheory Limits Opposite Simplicial MorphismProperty HomotopicalAlgebra
open Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open PastingDiagram

variable {p : Under pointPair.{u}}

private theorem equiv_boundary_of_eq {X : DiagSet.{u}} (a : PastingDiagram X) {k m : ℕ} (h : k = m)
    (α : Bool) : (a.boundary k α).Equiv (a.boundary m α) := by
  subst h
  exact .refl _

private theorem equiv_paste_of_eq {X : DiagSet.{u}} {a b : PastingDiagram X} {k m : ℕ} (h : k = m)
    (hk : a.Pastable b k) (hm : a.Pastable b m) : (a.paste b k hk).Equiv (a.paste b m hm) := by
  subst h
  exact .refl _

private theorem equiv_suspension_paste_cond (α : Bool) {a b : PastingDiagram (bipointedHom.obj p)}
    {k m : ℕ} (hm : m = k + 1) (h : (cond α a b).Pastable (cond α b a) k)
    (h' : (cond α a.suspension b.suspension).Pastable (cond α b.suspension a.suspension) m) :
    ((cond α a.suspension b.suspension).paste (cond α b.suspension a.suspension) m h').Equiv
      ((cond α a b).paste (cond α b a) k h).suspension := by
  subst hm
  cases α
  · exact (Equiv.paste (.refl _) (.refl _) _ h.suspension).trans (equiv_suspension_paste h)
  · exact (Equiv.paste (.refl _) (.refl _) _ h.suspension).trans (equiv_suspension_paste h)

private noncomputable def BiInvData.suspension {A : Set (RoundPastingDiagram (bipointedHom.obj p))}
    {e : RoundPastingDiagram (bipointedHom.obj p)} (d : BiInvData A e) :
    BiInvData (RoundPastingDiagram.suspension '' A) e.suspension :=
  have hd : e.suspension.dim = e.dim + 1 := dim_suspension _
  have hk : e.suspension.dim - 1 = (e.dim - 1) + 1 := by have := d.dim_pos; omega
  { dim_pos := by omega
    inverse := fun α => (d.inverse α).suspension
    invertor := fun α => (d.invertor α).suspension
    invertor_mem := fun α => ⟨_, d.invertor_mem α, rfl⟩
    dim_inverse := fun α => (dim_suspension _).trans ((congrArg (· + 1) (d.dim_inverse α)).trans
      hd.symm)
    dim_invertor := fun α => (dim_suspension _).trans ((congrArg (· + 1) (d.dim_invertor α)).trans
      (congrArg (· + 1) hd.symm))
    equiv_boundary_inverse := fun α γ => by
      rw [hk]
      exact (equiv_boundary_suspension _ _ γ).trans ((d.equiv_boundary_inverse α γ).suspension.trans
        (equiv_boundary_suspension _ _ _).symm)
    pastable := fun α => by
      rw [hk]
      cases α
      exacts [(d.pastable false).suspension, (d.pastable true).suspension]
    boundary_invertor_composite := fun α =>
      (equiv_boundary_of_eq (d.invertor α).toPastingDiagram.suspension hd α).trans
        ((equiv_boundary_suspension (d.invertor α).toPastingDiagram e.dim α).trans
        ((d.boundary_invertor_composite α).suspension.trans
        (equiv_suspension_paste_cond α hk (d.pastable α) _).symm))
    boundary_invertor_unit := fun α =>
      (equiv_boundary_of_eq (d.invertor α).toPastingDiagram.suspension hd (!α)).trans
        ((equiv_boundary_suspension (d.invertor α).toPastingDiagram e.dim (!α)).trans
        ((d.boundary_invertor_unit α).suspension.trans ((equiv_suspension_unit _).trans
        ((equiv_boundary_of_eq e.toPastingDiagram.suspension hk α).trans
          (equiv_boundary_suspension _ _ α)).symm.unit))) }

theorem suspension_mem_equivalences {e : RoundPastingDiagram (bipointedHom.obj p)}
    (he : e ∈ equivalences (bipointedHom.obj p)) : e.suspension ∈ equivalences p.right :=
  subset_equivalences (A := RoundPastingDiagram.suspension '' equivalences (bipointedHom.obj p))
    (by
      rintro _ ⟨e, he, rfl⟩
      exact (BiInvData.suspension ((mem_equivalences_iff e).1 he).data).witness)
    ⟨e, he, rfl⟩

private theorem nonempty_biInvData_of_suspension (hX : HasWeakComposites p.right)
    {e : RoundPastingDiagram (bipointedHom.obj p)} (hpos : 0 < e.dim)
    (he : e.suspension ∈ equivalences p.right) :
    Nonempty (BiInvData {d : RoundPastingDiagram (bipointedHom.obj p) |
      0 < d.dim ∧ d.suspension ∈ equivalences p.right} e) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero hpos.ne'
  obtain ⟨d, hinv, hinvt⟩ := exists_cellular_biInvData hX he
  choose U c hc using hinv
  choose V w hw using hinvt
  have hd : e.suspension.dim = n + 2 := (dim_suspension _).trans (by rw [hn])
  have hk : e.suspension.dim - 1 = n + 1 := by omega
  have hdU (α : Bool) : (U α).dimension = n + 2 :=
    (congrArg (·.dim) (hc α)).symm.trans ((d.dim_inverse α).trans hd)
  have hdV (α : Bool) : (V α).dimension = n + 3 :=
    (congrArg (·.dim) (hw α)).symm.trans ((d.dim_invertor α).trans (by rw [hd]))
  have hbi (α γ : Bool) : ((ofCell (c α)).boundary (n + 1) γ).Equiv
      (e.boundary n (!γ)).suspension := by
    have h := d.equiv_boundary_inverse α γ
    rw [hk, hc α] at h
    exact h.trans (equiv_boundary_suspension _ _ _)
  choose U' c' hc' using fun α => exists_cell_equiv_suspension (c α) (hdU α) _ (hbi α)
  have hdc' (α : Bool) : (cellRound (c' α)).dim = e.dim := by
    have h := dim_eq_of_equiv (hc' α)
    rw [dim_suspension] at h
    have h' : (ofCell (c α)).dim = n + 2 := hdU α
    change (ofCell (c' α)).dim = e.dim
    omega
  have hb (α γ : Bool) : ((cellRound (c' α)).boundary (e.dim - 1) γ).Equiv
      (e.boundary (e.dim - 1) (!γ)) := by
    rw [hn, Nat.add_sub_cancel]
    exact suspension_equiv_suspension_iff.1 ((equiv_boundary_suspension _ n γ).symm.trans
      (((hc' α).boundary (n + 1) γ).trans (hbi α γ)))
  have hp (α : Bool) : (cond α (cellRound (c' α)).toPastingDiagram e.toPastingDiagram).Pastable
      (cond α e.toPastingDiagram (cellRound (c' α)).toPastingDiagram) (e.dim - 1) :=
    Pastable.of_side α (hb α α) (by rw [hdc']; omega) (by omega)
  have hpn (α : Bool) : (cond α (cellRound (c' α)).toPastingDiagram e.toPastingDiagram).Pastable
      (cond α e.toPastingDiagram (cellRound (c' α)).toPastingDiagram) n := by
    have h := hp α
    rwa [hn, Nat.add_sub_cancel] at h
  let a (α β : Bool) : PastingDiagram (bipointedHom.obj p) :=
    if β = α then (cond α (cellRound (c' α)).toPastingDiagram e.toPastingDiagram).paste
      (cond α e.toPastingDiagram (cellRound (c' α)).toPastingDiagram) n (hpn α)
    else (e.boundary n α).unit
  have hbw (α β : Bool) : ((ofCell (w α)).boundary (n + 2) β).Equiv (a α β).suspension := by
    obtain rfl | rfl : β = α ∨ β = !α := by cases β <;> cases α <;> simp
    · have h0 : ((ofCell (w β)).boundary (n + 2) β).Equiv
          ((d.invertor β).boundary e.suspension.dim β) := by
        rw [hw β, hd]
        exact .refl _
      rw [show a β β = _ from if_pos rfl]
      have hcs : (cond β (d.inverse β).toPastingDiagram e.suspension.toPastingDiagram).Equiv
          (cond β (cellRound (c' β)).toPastingDiagram.suspension
            e.toPastingDiagram.suspension) := by
        rw [hc β]
        cases β
        exacts [.refl _, (hc' true).symm]
      have hcs' : (cond β e.suspension.toPastingDiagram (d.inverse β).toPastingDiagram).Equiv
          (cond β e.toPastingDiagram.suspension
            (cellRound (c' β)).toPastingDiagram.suspension) := by
        rw [hc β]
        cases β
        exacts [(hc' false).symm, .refl _]
      have hq := (d.pastable β).of_equiv hcs hcs'
      have hq' : (cond β (cellRound (c' β)).toPastingDiagram.suspension
          e.toPastingDiagram.suspension).Pastable
          (cond β e.toPastingDiagram.suspension (cellRound (c' β)).toPastingDiagram.suspension)
          (n + 1) := by
        rw [hk] at hq
        exact hq
      exact h0.trans ((d.boundary_invertor_composite β).trans ((Equiv.paste hcs hcs' _ hq).trans
        ((equiv_paste_of_eq hk hq hq').trans (equiv_suspension_paste_cond β rfl (hpn β) hq'))))
    · have h0 : ((ofCell (w α)).boundary (n + 2) (!α)).Equiv
          ((d.invertor α).boundary e.suspension.dim (!α)) := by
        rw [hw α, hd]
        exact .refl _
      rw [show a α (!α) = _ from if_neg (by cases α <;> simp)]
      exact h0.trans ((d.boundary_invertor_unit α).trans
        (((equiv_boundary_of_eq e.toPastingDiagram.suspension hk α).trans
          (equiv_boundary_suspension _ _ _)).unit.trans (equiv_suspension_unit _).symm))
  choose V' w' hw' using fun α => exists_cell_equiv_suspension (w α) (hdV α) _ (hbw α)
  have hdw' (α : Bool) : (cellRound (w' α)).dim = n + 2 := by
    have h := dim_eq_of_equiv (hw' α)
    rw [dim_suspension] at h
    have h' : (ofCell (w α)).dim = n + 3 := hdV α
    change (ofCell (w' α)).dim = n + 2
    omega
  have hbw' (α β : Bool) : ((cellRound (w' α)).boundary (n + 1) β).Equiv (a α β) :=
    suspension_equiv_suspension_iff.1 ((equiv_boundary_suspension _ _ β).symm.trans
      (((hw' α).boundary (n + 2) β).trans (hbw α β)))
  refine ⟨{ dim_pos := hpos
            inverse := fun α => cellRound (c' α)
            invertor := fun α => cellRound (w' α)
            invertor_mem := fun α => ⟨by rw [hdw']; omega, mem_equivalences_of_equiv
              (e := cellRound (w α)) (hw' α).symm (by rw [← hw α]; exact d.invertor_mem α)⟩
            dim_inverse := hdc'
            dim_invertor := fun α => (hdw' α).trans (by rw [hn])
            equiv_boundary_inverse := hb
            pastable := hp
            boundary_invertor_composite := fun α => ?_
            boundary_invertor_unit := fun α => ?_ }⟩
  · have h := hbw' α α
    rw [show a α α = _ from if_pos rfl] at h
    exact (equiv_boundary_of_eq (cellRound (w' α)).toPastingDiagram hn α).trans
      (h.trans (equiv_paste_of_eq (by omega) _ _))
  · have h := hbw' α (!α)
    rw [show a α (!α) = _ from if_neg (by cases α <;> simp)] at h
    rw [hn, Nat.add_sub_cancel]
    exact h

theorem mem_equivalences_bipointedHom_iff (hX : HasWeakComposites p.right)
    (e : RoundPastingDiagram (bipointedHom.obj p)) (hpos : 0 < e.dim) :
    e ∈ equivalences (bipointedHom.obj p) ↔ e.suspension ∈ equivalences p.right :=
  ⟨suspension_mem_equivalences, fun he => subset_equivalences
    (A := {d : RoundPastingDiagram (bipointedHom.obj p) |
      0 < d.dim ∧ d.suspension ∈ equivalences p.right})
    (fun _ hd => (nonempty_biInvData_of_suspension hX hd.1 hd.2).some.witness) ⟨hpos, he⟩⟩

theorem isEquivalence_bipointedHom_iff (hX : HasWeakComposites p.right) {U : Atom}
    (c : diagram (bipointedHom.obj p) U) (hU : 0 < U.dimension) :
    IsEquivalence (bipointedHom.obj p) c ↔
      IsEquivalence p.right (uliftYonedaEquiv (bipointedHomObjEquiv p U c).1) :=
  (mem_equivalences_bipointedHom_iff hX (cellRound c) hU).trans
    ⟨mem_equivalences_of_equiv (equiv_suspension_ofCell c),
      mem_equivalences_of_equiv (equiv_suspension_ofCell c).symm⟩

theorem hasWeakComposites_bipointedHom (hX : HasWeakComposites p.right) :
    HasWeakComposites (bipointedHom.obj p) := by
  rw [hasWeakComposites_iff_positive]
  intro u hu
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero hu.ne'
  have hsd : u.suspension.dim = m + 2 := (dim_suspension _).trans (by rw [hm])
  have hspos : 0 < u.suspension.dim := by omega
  obtain ⟨c, hc⟩ := (hasWeakComposites_iff_positive _).1 hX u.suspension hspos
  have hdc : (mergerAtom u.suspension.roundShape hspos).dimension = m + 2 :=
    hc.data.dim_eq.symm.trans hsd
  have hbc (γ : Bool) : ((ofCell c).boundary (m + 1) γ).Equiv (u.boundary m γ).suspension :=
    (hc.equiv_boundary (by omega) γ).symm.trans (equiv_boundary_suspension _ _ _)
  obtain ⟨U, d, hd⟩ := exists_cell_equiv_suspension c hdc _ hbc
  have hdU : U.dimension = m + 1 := by
    have h := dim_eq_of_equiv hd
    rw [dim_suspension] at h
    have h' : (ofCell c).dim = m + 2 := hdc
    change (ofCell d).dim = m + 1
    omega
  set M := mergerAtom u.roundShape hu
  have hbd (γ : Bool) : ((ofCell d).boundary m γ).Equiv (u.boundary m γ) :=
    suspension_equiv_suspension_iff.1 ((equiv_boundary_suspension _ _ γ).symm.trans
      ((hd.boundary (m + 1) γ).trans (hbc γ)))
  have hφ (γ : Bool) : Nonempty ((U.toMoleculeShape.boundary m γ).ogp ≅
      (M.toMoleculeShape.boundary m γ).ogp) := by
    have e := mergerAtomBoundaryIso u.roundShape hu γ
    have hm' : u.roundShape.dimension - 1 = m := by
      change u.dim - 1 = m
      omega
    rw [hm'] at e
    exact ⟨(hbd γ).iso ≪≫ e.symm⟩
  obtain ⟨θ⟩ := MoleculeShape.nonempty_iso_of_boundary_iso U.toMoleculeShape M.toMoleculeShape
    (fun γ => (hφ γ).some) U.isAtom M.isAtom hdU
    ((dimension_mergerAtom _ _).trans hm)
  set d' := (bipointedHom.obj p).map (Atom.isoOfOGPIso θ).symm.hom.op d
  have hd' : (ofCell d').Equiv (ofCell d) := equiv_ofCell_map_iso _ d
  refine ⟨d', ?_⟩
  obtain ⟨V, w, hw, hdV, hs, ht⟩ := exists_equivalence_cell_side hX false _ _ hc
  rw [hsd] at hdV hs ht
  have hbw (γ : Bool) : ((ofCell w).boundary (m + 1 + 1) γ).Equiv
      (cond γ (ofCell d') u.toPastingDiagram).suspension := by
    cases γ
    exacts [hs, ht.trans (hd.symm.trans hd'.symm.suspension)]
  obtain ⟨Z, z, hz⟩ := exists_cell_equiv_suspension w hdV _ hbw
  have hdz : (cellRound z).dim = m + 2 := by
    have h := dim_eq_of_equiv hz
    rw [dim_suspension] at h
    have h' : (ofCell w).dim = m + 3 := hdV
    change (ofCell z).dim = m + 2
    omega
  have hbz (γ : Bool) : ((cellRound z).boundary (m + 1) γ).Equiv
      (cond γ (ofCell d') u.toPastingDiagram) :=
    suspension_equiv_suspension_iff.1 ((equiv_boundary_suspension _ _ γ).symm.trans
      ((hz.boundary (m + 1 + 1) γ).trans (hbw γ)))
  refine EquivalenceData.equivalent
    { dim_eq := (dimension_mergerAtom u.roundShape hu).symm
      equivalence := cellRound z
      mem := (mem_equivalences_bipointedHom_iff hX _ (by omega)).2
        (mem_equivalences_of_equiv hz.symm hw)
      dim_equivalence := hdz.trans (by rw [hm])
      source := by rw [hm]; exact hbz false
      target := by rw [hm]; exact hbz true }

open HomotopicalAlgebra

theorem isInftyCategory_bipointedHom {n : ℕ∞} {p : Under pointPair.{u}}
    (hX : IsInftyCategory (n + 1) p.right) : IsInftyCategory n (bipointedHom.obj p) := by
  refine ⟨hasWeakComposites_bipointedHom hX.1, fun U c hU => ?_⟩
  have hpos : 0 < U.dimension := Nat.cast_pos.1 (zero_le.trans_lt hU)
  refine (isEquivalence_bipointedHom_iff hX.1 c hpos).2 (hX.2 _ _ ?_)
  rw [dimension_atomSuspension, Nat.cast_add, Nat.cast_one]
  exact (ENat.add_lt_add_iff_right ENat.one_ne_top).2 hU

theorem isFibrant_bipointedHom {p : Under pointPair.{u}} (hX : IsInftyCategory 1 p.right) :
    IsFibrant ((DiagSet.toInfty 0).obj (bipointedHom.obj p)) :=
  (isFibrant_infty_iff 0 _).2 (isInftyCategory_bipointedHom (n := 0) (by simpa using hX))

theorem Equivalent.suspension {u v : RoundPastingDiagram (bipointedHom.obj p)}
    (h : Equivalent u v) : Equivalent u.suspension v.suspension := by
  obtain ⟨hd, e, he, hed, h₁, h₂⟩ := h.data
  have hu : u.suspension.dim = u.dim + 1 := dim_suspension _
  refine EquivalenceData.equivalent
    ⟨by rw [hu, RoundPastingDiagram.suspension_toPastingDiagram, dim_suspension, hd],
      e.suspension, suspension_mem_equivalences he, ?_, ?_, ?_⟩
  · rw [RoundPastingDiagram.suspension_toPastingDiagram, dim_suspension, hed, hu]
  · exact (equiv_boundary_of_eq _ hu false).trans
      ((equiv_boundary_suspension _ _ false).trans h₁.suspension)
  · exact (equiv_boundary_of_eq _ hu true).trans
      ((equiv_boundary_suspension _ _ true).trans h₂.suspension)

theorem equivalent_suspension_iff (hX : HasWeakComposites p.right)
    (u v : RoundPastingDiagram (bipointedHom.obj p)) :
    Equivalent u.suspension v.suspension ↔ Equivalent u v := by
  refine ⟨fun h => ?_, Equivalent.suspension⟩
  have hu : u.suspension.dim = u.dim + 1 := dim_suspension _
  have hv : v.dim = u.dim := by
    have := h.data.dim_eq
    rw [hu, RoundPastingDiagram.suspension_toPastingDiagram, dim_suspension] at this
    omega
  obtain ⟨V, c, hc, hV, hc₁, hc₂⟩ := exists_equivalence_cell_side hX false _ _ h
  rw [hu] at hV hc₁ hc₂
  have ha : ∀ α, ((ofCell c).boundary (u.dim + 1) α).Equiv
      (cond α v.toPastingDiagram u.toPastingDiagram).suspension := fun α => by
    cases α
    exacts [hc₁, hc₂]
  obtain ⟨U, d, hd⟩ := exists_cell_equiv_suspension c hV _ ha
  have hdd : (ofCell d).dim = u.dim + 1 := by
    have := dim_eq_of_equiv hd
    rw [dim_suspension] at this
    have hc' : (ofCell c).dim = V.dimension := rfl
    omega
  have hz : cellRound d ∈ equivalences (bipointedHom.obj p) :=
    (mem_equivalences_bipointedHom_iff hX (cellRound d) (by
      change 0 < (ofCell d).dim
      omega)).2 (mem_equivalences_of_equivalent (equivalent_of_equiv (v := cellRound c) hd) hc)
  have hb (α : Bool) : ((cellRound d).boundary u.dim α).Equiv
      (cond α v.toPastingDiagram u.toPastingDiagram) :=
    suspension_equiv_suspension_iff.1 ((equiv_boundary_suspension _ _ α).symm.trans
      ((hd.boundary _ α).trans (ha α)))
  exact equivalent_of_mem_equivalences_cond false hz rfl hv hdd (hb false) (hb true)

section Vertices

variable {X Y : DiagSet.{u}}

private theorem face_comp_hom_eq (φ : atomSimplex 1 ≅ atomSuspension.obj (atomSimplex 0))
    (α : Bool) :
    simplexHom (SimplexCategory.δ (cond α 0 1 : Fin 2)).toOrderHom ≫ φ.hom =
      toAtomPoint (atomSimplex 0) ≫ suspPole (atomSimplex 0) α := by
  have hsurj : Function.Surjective φ.hom := fun y =>
    ⟨φ.inv y, by rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id]; rfl⟩
  have htop : φ.hom (atomSimplex 1).top = (atomSuspension.obj (atomSimplex 0)).top :=
    IsCollapseHom.apply_top (f := φ.hom) hsurj
  have hW : ((atomSuspension.obj (atomSimplex 0)).ogp.boundary ⊤ 0 α :
      LowerSet (atomSuspension.obj (atomSimplex 0)).ogp) =
      LowerSet.Iic ((FiniteOGP.ofOGPIso (suspension (atomSimplex 0).ogp)).hom
        (SuspCarrier.pole α)) := by
    have hb := map_boundary (FiniteOGP.ofOGPIso (suspension (atomSimplex 0).ogp)).hom ⊤ 0 α
    rw [map_top_of_isIso, ← susp_top,
      boundary_susp_zero ⟨(atomSimplex 0).top, by simp⟩, map_Iic] at hb
    exact hb.symm
  refine Atom.hom_ext fun z => ?_
  have hz : z = (atomSimplex 0).top := by
    by_contra hne
    have := grade_strictMono (𝕆 := ℕ) (lt_of_le_of_ne ((atomSimplex 0).le_top z) hne)
    rw [← Atom.dimension_eq, dimension_atomSimplex] at this
    omega
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, suspPole_apply, hz]
  have hv := boundary_univ_zero_atomSimplex_one α
  have h := (Atom.isMap φ.hom).image_boundary (atomSimplex 1).top 0 α
  rw [Atom.Iic_top, hv, LowerSet.coe_Iic, (Atom.isMap φ.hom).image_Iic, htop, Atom.Iic_top,
    hW] at h
  exact le_antisymm (LowerSet.mem_Iic_iff.1 ((Set.ext_iff.1 h _).1 (Set.mem_Iic.2 le_rfl)))
    (Set.mem_Iic.1 ((Set.ext_iff.1 h _).2 (LowerSet.mem_Iic_iff.2 le_rfl)))

noncomputable def DiagSet.bipoint (X : DiagSet.{u}) (x y : X.Vertex) : Under pointPair.{u} :=
  Under.mk (coprod.desc (vertexHom x) (vertexHom y))

@[simp] theorem DiagSet.bipoint_right (X : DiagSet.{u}) (x y : X.Vertex) :
    (X.bipoint x y).right = X :=
  rfl

noncomputable def DiagSet.bipointMap (F : X ⟶ Y) (x y : X.Vertex) :
    X.bipoint x y ⟶ Y.bipoint (x.map F) (y.map F) :=
  Under.homMk F (coprod.hom_ext
    (by simp only [DiagSet.bipoint, Under.mk_hom, coprod.inl_desc_assoc, coprod.inl_desc,
      vertexHom_comp])
    (by simp only [DiagSet.bipoint, Under.mk_hom, coprod.inr_desc_assoc, coprod.inr_desc,
      vertexHom_comp]))

@[simp] theorem DiagSet.bipointMap_right (F : X ⟶ Y) (x y : X.Vertex) :
    (DiagSet.bipointMap F x y).right = F :=
  rfl

private noncomputable def intervalSuspIso : atomSimplex 1 ≅ atomSuspension.obj (atomSimplex 0) :=
  Classical.choice (by
    obtain ⟨k, ⟨e⟩⟩ := exists_nonempty_iso_cone_simplexFunctor_obj
      (B := atomSuspension.obj (atomSimplex 0))
      (by rw [dimension_atomSuspension, dimension_atomSimplex]) 0
    have hk : k.len = 1 := by
      have h := Atom.dimension_eq_of_iso e
      change (atomSuspension.obj (atomSimplex 0)).dimension = (atomSimplex k.len).dimension at h
      rw [dimension_atomSimplex, dimension_atomSuspension, dimension_atomSimplex] at h
      exact h.symm
    have ek : simplexFunctor.obj k = atomSimplex 1 := by
      change atomSimplex k.len = atomSimplex 1
      rw [hk]
    exact ⟨(e ≪≫ eqToIso ek).symm⟩)

private theorem suspendedBallPoles_comp_eq_iff (x y : X.Vertex)
    (f : ball.{u} (atomSuspension.obj (atomSimplex 0)) ⟶ X) :
    suspendedBallPoles (atomSimplex 0) ≫ f = coprod.desc (vertexHom x) (vertexHom y) ↔
      intervalSource ≫ uliftYoneda.map intervalSuspIso.hom ≫ f = vertexHom x ∧
        intervalTarget ≫ uliftYoneda.map intervalSuspIso.hom ≫ f = vertexHom y := by
  have hface (α : Bool) :
      uliftYoneda.map (simplexHom (SimplexCategory.δ (cond α 0 1 : Fin 2)).toOrderHom) ≫
        uliftYoneda.map intervalSuspIso.hom ≫ f =
      uliftYoneda.{u}.map (suspPole (atomSimplex 0) α) ≫ f := by
    have h : toAtomPoint (atomSimplex 0) ≫ suspPole (atomSimplex 0) α =
        suspPole (atomSimplex 0) α :=
      (congrArg (· ≫ suspPole (atomSimplex 0) α)
        (Subsingleton.elim (toAtomPoint (atomSimplex 0)) (𝟙 atomPoint))).trans (Category.id_comp _)
    rw [← Category.assoc, ← Functor.map_comp, face_comp_hom_eq, h]
    rfl
  have h0 : intervalSource ≫ uliftYoneda.map intervalSuspIso.hom ≫ f =
      uliftYoneda.{u}.map (suspPole (atomSimplex 0) false) ≫ f := hface false
  have h1 : intervalTarget ≫ uliftYoneda.map intervalSuspIso.hom ≫ f =
      uliftYoneda.{u}.map (suspPole (atomSimplex 0) true) ≫ f := hface true
  rw [h0, h1]
  rw [suspendedBallPoles, coprod.desc_comp]
  constructor
  · intro h
    have h₁ := congrArg (coprod.inl ≫ ·) h
    have h₂ := congrArg (coprod.inr ≫ ·) h
    rw [coprod.inl_desc, coprod.inl_desc] at h₁
    rw [coprod.inr_desc, coprod.inr_desc] at h₂
    exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    rw [h₁, h₂]

private noncomputable def edgeEquivBallHom (x y : X.Vertex) :
    SSet.Edge (X.vertexEquivSSet x) (X.vertexEquivSSet y) ≃
      {e : ball.{u} (atomSimplex 1) ⟶ X //
      intervalSource ≫ e = vertexHom x ∧ intervalTarget ≫ e = vertexHom y} where
  toFun f := ⟨uliftYonedaEquiv.symm (f.edge : diagram X (atomSimplex 1)),
    (uliftYonedaEquiv_symm_map (F := X) (simplexHom (SimplexCategory.δ 1).toOrderHom).op
      f.edge).symm.trans (congrArg _ f.src_eq),
    (uliftYonedaEquiv_symm_map (F := X) (simplexHom (SimplexCategory.δ 0).toOrderHom).op
      f.edge).symm.trans (congrArg _ f.tgt_eq)⟩
  invFun e := SSet.Edge.mk (uliftYonedaEquiv e.1 : diagram X (atomSimplex 1))
    ((uliftYonedaEquiv_naturality (F := X) e.1 _).trans ((congrArg uliftYonedaEquiv e.2.1).trans
      (Equiv.apply_symm_apply _ _)))
    ((uliftYonedaEquiv_naturality (F := X) e.1 _).trans ((congrArg uliftYonedaEquiv e.2.2).trans
      (Equiv.apply_symm_apply _ _)))
  left_inv _ := SSet.Edge.ext (Equiv.apply_symm_apply _ _)
  right_inv _ := Subtype.ext (Equiv.symm_apply_apply _ _)

noncomputable def DiagSet.bipointedHomVerticesEquiv (x y : X.Vertex) :
    (bipointedHom.obj (X.bipoint x y)).Vertex ≃ X.Edge x y :=
  ((bipointedHomObjEquiv (X.bipoint x y) (atomSimplex 0)).trans
    ((Equiv.subtypeEquiv
      { toFun f := uliftYoneda.map intervalSuspIso.hom ≫ f
        invFun e := uliftYoneda.map intervalSuspIso.inv ≫ e
        left_inv f := by simp [← Functor.map_comp_assoc]
        right_inv e := by simp [← Functor.map_comp_assoc] }
      fun f => suspendedBallPoles_comp_eq_iff x y f).trans
        (edgeEquivBallHom x y).symm)).trans X.edgeEquivSSet.symm

theorem DiagSet.bipointedHomVerticesEquiv_edge (x y : X.Vertex)
    (v : (bipointedHom.obj (X.bipoint x y)).Vertex) :
    (X.edgeEquivSSet (X.bipointedHomVerticesEquiv x y v)).edge = X.map intervalSuspIso.hom.op
      (uliftYonedaEquiv (bipointedHomObjEquiv (X.bipoint x y) (atomSimplex 0) v).1) :=
  (congrArg SSet.Edge.edge (Equiv.apply_symm_apply _ _)).trans
    (uliftYonedaEquiv_naturality (F := X) _ _).symm

theorem DiagSet.nonempty_edge_iff_equivalent {Z : DiagSet.{u}} (hZ : IsInftyCategory 0 Z)
    (a b : Z.Vertex) :
    Nonempty (Z.Edge a b) ↔ Equivalent (cellRound a) (cellRound b) := by
  constructor
  · rintro ⟨e⟩
    have hs := hZ.2 (atomGlobe 1) e.cell
      (by rw [dimension_atomGlobe]; exact_mod_cast zero_lt_one)
    have hb := hasBdry_ofCell_edge e
    exact equivalent_of_mem_equivalences_cond false hs dimension_atomPoint dimension_atomPoint
      hb.dim_h hb.side hb.other
  · intro h
    obtain ⟨hd, e, he, hed, h₁, h₂⟩ := h.data
    have h0 : (cellRound a).dim = 0 := dimension_atomPoint
    rw [h0] at hed h₁
    rw [h0] at h₂
    obtain ⟨f, -⟩ := exists_edge_equivalent_of_hasBdry hZ.1 e
      ⟨hed, dimension_atomPoint, dimension_atomPoint, h₁, h₂⟩
    exact ⟨f⟩

variable {x y : X.Vertex}

private theorem equiv_suspension_ofCell_vertex (v : (bipointedHom.obj (X.bipoint x y)).Vertex) :
    (ofCell v).suspension.Equiv (ofCell (X.bipointedHomVerticesEquiv x y v).cell) :=
  ((equiv_suspension_ofCell _).trans ((equiv_ofCell_map_iso intervalSuspIso _).symm.trans
    (ofCell_equiv_ofCell_iff.2 (DiagSet.bipointedHomVerticesEquiv_edge x y v).symm))).trans
    (equiv_ofCell_edgeEquivSSet _)

private theorem equivalent_suspension_vertex (v : (bipointedHom.obj (X.bipoint x y)).Vertex) :
    Equivalent (cellRound v).suspension
      (cellRound (X := (X.bipoint x y).right) (X.bipointedHomVerticesEquiv x y v).cell) :=
  equivalent_of_equiv (equiv_suspension_ofCell_vertex v)

private theorem nonempty_edge_iff_equivalent_edge (hX : IsInftyCategory 1 X)
    (v w : (bipointedHom.obj (X.bipoint x y)).Vertex) :
    Nonempty ((bipointedHom.obj (X.bipoint x y)).Edge v w) ↔
      Equivalent (cellRound (X := X) (X.bipointedHomVerticesEquiv x y v).cell)
        (cellRound (X.bipointedHomVerticesEquiv x y w).cell) := by
  have hH : IsInftyCategory 0 (bipointedHom.obj (X.bipoint x y)) :=
    isInftyCategory_bipointedHom (n := 0) (by simpa using hX)
  have hv := equivalent_suspension_vertex v
  have hw := equivalent_suspension_vertex w
  rw [DiagSet.nonempty_edge_iff_equivalent hH, ← equivalent_suspension_iff hX.1]
  exact ⟨fun h => equivalent_trans (equivalent_symm hv) (equivalent_trans h hw),
    fun h => equivalent_trans hv (equivalent_trans h (equivalent_symm hw))⟩

theorem DiagSet.nonempty_edge_bipointedHom_iff (hX : IsInftyCategory 1 X) (f g : X.Edge x y) :
    Nonempty ((bipointedHom.obj (X.bipoint x y)).Edge ((X.bipointedHomVerticesEquiv x y).symm f)
        ((X.bipointedHomVerticesEquiv x y).symm g)) ↔
      Equivalent (cellRound f.cell) (cellRound g.cell) := by
  have h := nonempty_edge_iff_equivalent_edge hX ((X.bipointedHomVerticesEquiv x y).symm f)
    ((X.bipointedHomVerticesEquiv x y).symm g)
  simpa only [Equiv.apply_symm_apply] using h

private theorem nonempty_edge_iff_homMk_eq (hX : IsInftyCategory 1 X)
    (v w : (bipointedHom.obj (X.bipoint x y)).Vertex) :
    Nonempty ((bipointedHom.obj (X.bipoint x y)).Edge v w) ↔
      HomotopyCategory.homMk hX.1 (X.bipointedHomVerticesEquiv x y v) =
        HomotopyCategory.homMk hX.1 (X.bipointedHomVerticesEquiv x y w) := by
  rw [HomotopyCategory.homMk_eq_homMk_iff]
  exact nonempty_edge_iff_equivalent_edge hX v w

private noncomputable def vertexClass (hX : IsInftyCategory 1 X)
    (v : (DiagSet.toSSet.obj (bipointedHom.obj (X.bipoint x y))) _⦋0⦌) :
    (⟨x⟩ : HomotopyCategory X hX.1) ⟶ ⟨y⟩ :=
  HomotopyCategory.homMk hX.1
    (X.bipointedHomVerticesEquiv x y ((DiagSet.vertexEquivSSet _).symm v))

private theorem vertexClass_eq_of_edge (hX : IsInftyCategory 1 X)
    {v w : (DiagSet.toSSet.obj (bipointedHom.obj (X.bipoint x y))) _⦋0⦌} (e : SSet.Edge v w) :
    vertexClass hX v = vertexClass hX w :=
  (nonempty_edge_iff_homMk_eq hX ((DiagSet.vertexEquivSSet _).symm v)
    ((DiagSet.vertexEquivSSet _).symm w)).1 ⟨DiagSet.edgeEquivSSet.symm e⟩

noncomputable def DiagSet.bipointedHomπ₀Equiv (hX : IsInftyCategory 1 X)
    (x y : X.Vertex) :
    SSet.π₀ (DiagSet.toSSet.obj (bipointedHom.obj (X.bipoint x y))) ≃
      ((⟨x⟩ : HomotopyCategory X hX.1) ⟶ ⟨y⟩) :=
  Equiv.ofBijective (SSet.π₀.lift (vertexClass hX) fun _ _ e => vertexClass_eq_of_edge hX e)
    ⟨fun a b hab => by
      induction a with | mk v => ?_
      induction b with | mk w => ?_
      rw [SSet.π₀.lift_mk, SSet.π₀.lift_mk] at hab
      obtain ⟨e⟩ := (nonempty_edge_iff_homMk_eq hX _ _).2 hab
      exact SSet.π₀.sound (DiagSet.edgeEquivSSet e),
    fun φ => by
      obtain ⟨f, rfl⟩ := HomotopyCategory.homMk_surjective hX.1 φ
      exact ⟨SSet.π₀.mk (DiagSet.vertexEquivSSet _ ((X.bipointedHomVerticesEquiv x y).symm f)), by
        rw [SSet.π₀.lift_mk, vertexClass, Equiv.symm_apply_apply, Equiv.apply_symm_apply]⟩⟩

theorem DiagSet.bipointedHomπ₀Equiv_mk (hX : IsInftyCategory 1 X) (x y : X.Vertex)
    (e : X.Edge x y) :
    X.bipointedHomπ₀Equiv hX x y (SSet.π₀.mk (DiagSet.vertexEquivSSet _
        ((X.bipointedHomVerticesEquiv x y).symm e))) = HomotopyCategory.homMk hX.1 e := by
  refine (SSet.π₀.lift_mk (vertexClass hX) (fun _ _ e => vertexClass_eq_of_edge hX e) _).trans ?_
  rw [vertexClass, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

end Vertices

theorem rlp_monomorphisms_bipointedHom_map {p q : Under pointPair.{u}} (f : p ⟶ q)
    (hf : (MorphismProperty.monomorphisms DiagSet.{u}).rlp f.right) :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp (bipointedHom.map f) := by
  rw [monomorphisms_eq_saturation_sphereInclusions, MorphismProperty.rlp_saturation]
  rintro _ _ _ ⟨U⟩
  rw [← bipointedSuspensionAdjunction.hasLiftingProperty_iff]
  have : HasLiftingProperty (Under.homMk (U := Under.mk (sphereSuspensionPoles.{u} U))
      (V := suspendedBall.obj U)
      (sphereInclusion (atomSuspension.obj U)) (sphereSuspensionPoles_comp U)) f :=
    @HasLiftingProperty.under _ _ _ _ _ _ _ _ _
      (hf (sphereInclusion (atomSuspension.obj U)) (monomorphisms.infer_property _))
  exact HasLiftingProperty.of_arrow_iso_left (hip := this)
    (Arrow.isoMk (bipointedSuspensionSphereIso U) (bipointedSuspensionBallIso U)
      (bipointedSuspension_map_sphereInclusion U).symm).symm f

theorem weakEquivalence_bipointedHom_map {p q : Under pointPair.{u}} (f : p ⟶ q)
    (hp : IsInftyCategory 1 p.right) (hq : IsInftyCategory 1 q.right)
    [WeakEquivalence ((DiagSet.toInfty 1).map f.right)] :
    WeakEquivalence ((DiagSet.toInfty 0).map (bipointedHom.map f)) := by
  let P : Under pointPair.{u} := Under.mk (p.hom ≫ reversibleMappingPathSpaceIncl f.right)
  let i : p ⟶ P := Under.homMk (reversibleMappingPathSpaceIncl f.right) rfl
  let r : P ⟶ p := Under.homMk (pullback.fst _ _) 
    ((Category.assoc _ _ _).trans ((congrArg (p.hom ≫ ·)
      (reversibleMappingPathSpaceIncl_fst f.right)).trans (Category.comp_id _)))
  let π : P ⟶ q := Under.homMk (reversibleMappingPathSpaceProj f.right) 
    ((Category.assoc _ _ _).trans ((congrArg (p.hom ≫ ·)
      (reversibleMappingPathSpaceIncl_proj f.right)).trans (Under.w f)))
  have hir : i ≫ r = 𝟙 p := by
    ext1
    exact reversibleMappingPathSpaceIncl_fst f.right
  have hiπ : i ≫ π = f := by
    ext1
    exact reversibleMappingPathSpaceIncl_proj f.right
  have hr : WeakEquivalence ((DiagSet.toInfty 0).map (bipointedHom.map r)) :=
    weakEquivalence_toInfty_map_of_rlp_monomorphisms 0 (rlp_monomorphisms_bipointedHom_map r
      (rlp_monomorphisms_reversibleMappingPathSpace_fst f.right 1 hq))
  have hπ : WeakEquivalence ((DiagSet.toInfty 0).map (bipointedHom.map π)) :=
    weakEquivalence_toInfty_map_of_rlp_monomorphisms 0 (rlp_monomorphisms_bipointedHom_map π
      (rlp_monomorphisms_reversibleMappingPathSpaceProj f.right 1 hp hq))
  have : WeakEquivalence ((DiagSet.toInfty 0).map (bipointedHom.map i)) := by
    have : WeakEquivalence ((DiagSet.toInfty 0).map (bipointedHom.map i) ≫
        (DiagSet.toInfty 0).map (bipointedHom.map r)) := by
      rw [← Functor.map_comp, ← Functor.map_comp, hir, CategoryTheory.Functor.map_id,
        CategoryTheory.Functor.map_id]
      infer_instance
    exact weakEquivalence_of_postcomp _ ((DiagSet.toInfty 0).map (bipointedHom.map r))
  rw [← hiπ, Functor.map_comp, Functor.map_comp]
  infer_instance

section Globular

variable {X : DiagSet.{u}} {x y : X.Vertex}

private noncomputable def vertexBicat (x : X.Vertex) : RoundBicat X 0 :=
  ⟨cellRound x, dimension_atomPoint⟩

theorem hasBdry_of_equivalent_edge {p : RoundPastingDiagram X}
    {f : X.Edge x y} (ep : Equivalent p (cellRound f.cell)) :
    HasBdry false 0 p.toPastingDiagram (ofCell x) (ofCell y) :=
  have hf := hasBdry_ofCell_edge f
  have hp : p.dim = 0 + 1 := ep.data.dim_eq.trans hf.dim_h
  ⟨hp, hf.dim_a, hf.dim_b, (ep.equiv_boundary (by omega) false).trans hf.side,
    (ep.equiv_boundary (by omega) true).trans hf.other⟩

private noncomputable def arrowOf {p : RoundPastingDiagram X}
    {f : X.Edge x y} (ep : Equivalent p (cellRound f.cell)) :
    vertexBicat x ⟶ vertexBicat y :=
  (⟨p, hasBdry_of_equivalent_edge ep⟩ : RoundBicat.Arrow (vertexBicat x) (vertexBicat y)).hom

private noncomputable def edgeArrow (f : X.Edge x y) : vertexBicat x ⟶ vertexBicat y :=
  (⟨cellRound f.cell, hasBdry_ofCell_edge f⟩ :
    RoundBicat.Arrow (vertexBicat x) (vertexBicat y)).hom

private theorem mem_arrowOf {p : RoundPastingDiagram X}
    {f : X.Edge x y} (ep : Equivalent p (cellRound f.cell)) :
    (arrowOf ep).Mem p.toPastingDiagram :=
  (RoundBicat.Arrow.mem_hom _ _).2 (.refl _)

private theorem mem_edgeArrow (f : X.Edge x y) : (edgeArrow f).Mem (ofCell f.cell) :=
  (RoundBicat.Arrow.mem_hom _ _).2 (.refl _)

private noncomputable def cellOf {a b : RoundBicat X 0} {f g : a ⟶ b} {p q : PastingDiagram X}
    (hp : f.Mem p) (hq : g.Mem q) (u : RoundPastingDiagram X)
    (hu : HasBdry false 1 u.toPastingDiagram p q) : RoundBicat.Cell f g where
  diag := u
  dim_diag := hu.dim_h
  source := hp.of_equiv hu.side.symm
  target := hq.of_equiv hu.other.symm

private theorem hasBdry_of_hasRoundType {u : PastingDiagram X} {p q : RoundPastingDiagram X}
    (hu : HasRoundType u p q) (hp : p.dim = 1) :
    HasBdry false 1 u p.toPastingDiagram q.toPastingDiagram :=
  ⟨hu.dim_eq.trans (congrArg (· + 1) hp), hp, hu.dim_eq_dim.symm.trans hp,
    hu.equiv_boundary_cond hp false, hu.equiv_boundary_cond hp true⟩

private noncomputable def equivCell {p : RoundPastingDiagram X}
    {f : X.Edge x y} (ep : Equivalent p (cellRound f.cell)) :
    RoundBicat.Cell (arrowOf ep) (edgeArrow f) :=
  cellOf (mem_arrowOf ep) (mem_edgeArrow f) ep.data.equivalence (hasBdry_of_hasRoundType
    ⟨ep.data.dim_equivalence, ep.data.dim_eq, ep.data.source, ep.data.target⟩
    (hasBdry_of_equivalent_edge ep).dim_h)

private noncomputable def equivIso {p : RoundPastingDiagram X}
    {f : X.Edge x y} (ep : Equivalent p (cellRound f.cell)) :
    arrowOf ep ≅ edgeArrow f :=
  haveI := (RoundBicat.isIso_homMk_iff (equivCell ep)).2 ep.data.mem
  asIso (RoundBicat.homMk (equivCell ep))

private noncomputable def conjHom {p q : RoundPastingDiagram X}
    {f g : X.Edge x y} (ep : Equivalent p (cellRound f.cell))
    (eq : Equivalent q (cellRound g.cell))
    (u : RoundPastingDiagram X) (hu : HasRoundType u.toPastingDiagram p q) :
    edgeArrow f ⟶ edgeArrow g :=
  (equivIso ep).inv ≫ RoundBicat.homMk (cellOf (mem_arrowOf ep) (mem_arrowOf eq) u
    (hasBdry_of_hasRoundType hu (hasBdry_of_equivalent_edge ep).dim_h)) ≫ (equivIso eq).hom

private theorem equiv_suspension_ofCell_symm (f : X.Edge x y) :
    (ofCell ((X.bipointedHomVerticesEquiv x y).symm f)).suspension.Equiv (ofCell f.cell) := by
  have h := equiv_suspension_ofCell_vertex ((X.bipointedHomVerticesEquiv x y).symm f)
  rwa [Equiv.apply_symm_apply] at h

theorem exists_edge_bipointedHom_equivalent (hX : HasWeakComposites X) {f g : X.Edge x y}
    (w : RoundPastingDiagram X) (hw : HasBdry false 1 w.toPastingDiagram (ofCell f.cell)
      (ofCell g.cell)) :
    ∃ e : (bipointedHom.obj (X.bipoint x y)).Edge ((X.bipointedHomVerticesEquiv x y).symm f)
        ((X.bipointedHomVerticesEquiv x y).symm g),
      Equivalent (cellRound e.cell).suspension w := by
  obtain ⟨c, hc⟩ := hX w
  have hdc : (mergerAtomAll w.roundShape).dimension = 0 + 2 := hc.data.dim_eq.symm.trans hw.dim_h
  let a : Bool → PastingDiagram (bipointedHom.obj (X.bipoint x y)) := fun γ =>
    ofCell (cond γ ((X.bipointedHomVerticesEquiv x y).symm g)
      ((X.bipointedHomVerticesEquiv x y).symm f) : diagram _ atomPoint)
  have hbc (γ : Bool) : ((ofCell c).boundary (0 + 1) γ).Equiv (a γ).suspension := by
    refine (hc.equiv_boundary (by rw [hw.dim_h]; omega) γ).symm.trans ?_
    cases γ
    exacts [hw.side.trans (equiv_suspension_ofCell_symm f).symm,
      hw.other.trans (equiv_suspension_ofCell_symm g).symm]
  obtain ⟨U, d, hd⟩ := exists_cell_equiv_suspension (p := X.bipoint x y) c hdc a hbc
  have hdd : (ofCell d).dim = 0 + 1 := by
    have h := dim_eq_of_equiv hd
    rw [dim_suspension] at h
    exact Nat.succ.inj (h.trans hdc)
  have hbd (γ : Bool) : ((ofCell d).boundary 0 γ).Equiv (a γ) :=
    suspension_equiv_suspension_iff.1 ((equiv_boundary_suspension _ 0 γ).symm.trans
      ((hd.boundary (0 + 1) γ).trans (hbc γ)))
  obtain ⟨e, he⟩ := exists_edge_equivalent_of_hasBdry (hasWeakComposites_bipointedHom hX)
    (cellRound d) ⟨hdd, dimension_atomPoint, dimension_atomPoint, hbd false, hbd true⟩
  exact ⟨e, equivalent_trans (equivalent_symm he.suspension)
    (equivalent_trans (equivalent_of_equiv (v := cellRound c) hd) (equivalent_symm hc))⟩

private noncomputable def homEdge (hX : HasWeakComposites X) {f g : X.Edge x y}
    (η : edgeArrow f ⟶ edgeArrow g) :
    (bipointedHom.obj (X.bipoint x y)).Edge ((X.bipointedHomVerticesEquiv x y).symm f)
        ((X.bipointedHomVerticesEquiv x y).symm g) :=
  (exists_edge_bipointedHom_equivalent hX (RoundBicat.homMk_surjective η).choose.diag
    ((RoundBicat.homMk_surjective η).choose.hasBdry (mem_edgeArrow f) (mem_edgeArrow g))).choose

private theorem equivalent_homEdge (hX : HasWeakComposites X) {f g : X.Edge x y}
    (t : RoundBicat.Cell (edgeArrow f) (edgeArrow g)) :
    Equivalent (cellRound (homEdge hX (RoundBicat.homMk t)).cell).suspension t.diag := by
  have h := RoundBicat.homMk_surjective (RoundBicat.homMk t)
  exact equivalent_trans (exists_edge_bipointedHom_equivalent hX h.choose.diag
    (h.choose.hasBdry (mem_edgeArrow f) (mem_edgeArrow g))).choose_spec
    ((RoundBicat.homMk_eq_homMk_iff _ _).1 h.choose_spec)

private theorem homMk_homEdge_eq_iff (hX : HasWeakComposites X)
    {f g : X.Edge x y} (η θ : edgeArrow f ⟶ edgeArrow g) :
    HomotopyCategory.homMk (hasWeakComposites_bipointedHom hX) (homEdge hX η) =
      HomotopyCategory.homMk (hasWeakComposites_bipointedHom hX) (homEdge hX θ) ↔ η = θ := by
  obtain ⟨t, rfl⟩ := RoundBicat.homMk_surjective η
  obtain ⟨s, rfl⟩ := RoundBicat.homMk_surjective θ
  rw [HomotopyCategory.homMk_eq_homMk_iff, ← equivalent_suspension_iff hX,
    RoundBicat.homMk_eq_homMk_iff]
  have ht := equivalent_homEdge hX t
  have hs := equivalent_homEdge hX s
  exact ⟨fun h => equivalent_trans (equivalent_symm ht) (equivalent_trans h hs),
    fun h => equivalent_trans ht (equivalent_trans h (equivalent_symm hs))⟩

private theorem homMk_homEdge_id (hX : HasWeakComposites X)
    (f : X.Edge x y) :
    HomotopyCategory.homMk (hasWeakComposites_bipointedHom hX) (homEdge hX (𝟙 (edgeArrow f))) =
      𝟙 _ := by
  have h := equivalent_homEdge hX
    (RoundBicat.Cell.unitOf (RoundBicat.Hom.mem_rep (edgeArrow f)) (RoundBicat.Hom.mem_rep _))
  rw [← RoundBicat.id_eq_homMk] at h
  rw [← HomotopyCategory.homMk_id, HomotopyCategory.homMk_eq_homMk_iff,
    ← equivalent_suspension_iff hX]
  refine equivalent_trans h (equivalent_symm (equivalent_of_equiv ?_))
  exact (equiv_ofCell_edge_id_unit _).suspension.trans
    ((equiv_suspension_unit _).trans ((equiv_suspension_ofCell_symm f).unit.trans
      ((mem_edgeArrow f).equiv (RoundBicat.Hom.mem_rep _)).unit))

variable (hX : IsInftyCategory 2 X)

noncomputable def globularEdge {p q : RoundPastingDiagram X}
    {f g : X.Edge x y} (ep : Equivalent p (cellRound f.cell))
    (eq : Equivalent q (cellRound g.cell))
    (u : RoundPastingDiagram X) (hu : HasRoundType u.toPastingDiagram p q) :
    (bipointedHom.obj (X.bipoint x y)).Edge ((X.bipointedHomVerticesEquiv x y).symm f)
        ((X.bipointedHomVerticesEquiv x y).symm g) :=
  homEdge hX.1 (conjHom ep eq u hu)

noncomputable def globularClass {p q : RoundPastingDiagram X}
    {f g : X.Edge x y} (ep : Equivalent p (cellRound f.cell))
    (eq : Equivalent q (cellRound g.cell))
    (u : RoundPastingDiagram X) (hu : HasRoundType u.toPastingDiagram p q) :
    (⟨(X.bipointedHomVerticesEquiv x y).symm f⟩ :
        HomotopyCategory (bipointedHom.obj (X.bipoint x y)) (hasWeakComposites_bipointedHom hX.1)) ⟶
      ⟨(X.bipointedHomVerticesEquiv x y).symm g⟩ :=
  HomotopyCategory.homMk _ (globularEdge hX ep eq u hu)

theorem globularClass_eq_iff {p q : RoundPastingDiagram X}
    {f g : X.Edge x y} (ep : Equivalent p (cellRound f.cell))
    (eq : Equivalent q (cellRound g.cell))
    (u v : RoundPastingDiagram X) (hu : HasRoundType u.toPastingDiagram p q)
    (hv : HasRoundType v.toPastingDiagram p q) :
    globularClass hX ep eq u hu = globularClass hX ep eq v hv ↔ Equivalent u v := by
  rw [globularClass, globularClass, globularEdge, globularEdge, homMk_homEdge_eq_iff, conjHom,
    conjHom, Iso.cancel_iso_inv_left, Iso.cancel_iso_hom_right, RoundBicat.homMk_eq_homMk_iff]
  rfl

theorem globularClass_unit {p : RoundPastingDiagram X}
    {f : X.Edge x y} (ep : Equivalent p (cellRound f.cell))
    (hu : HasRoundType p.isRound.unit.toPastingDiagram p p) :
    globularClass hX ep ep p.isRound.unit hu = 𝟙 _ := by
  have hc : conjHom ep ep p.isRound.unit hu = 𝟙 (edgeArrow f) := by
    rw [conjHom]
    rw [show RoundBicat.homMk (cellOf (mem_arrowOf ep) (mem_arrowOf ep) p.isRound.unit
      (hasBdry_of_hasRoundType hu (hasBdry_of_equivalent_edge ep).dim_h)) = 𝟙 _ by
        rw [RoundBicat.id_eq_homMk, RoundBicat.homMk_eq_homMk_iff]
        exact equivalent_of_equiv ((mem_arrowOf ep).equiv (RoundBicat.Hom.mem_rep _)).unit,
      Category.id_comp, Iso.inv_hom_id]
  rw [globularClass, globularEdge, hc]
  exact homMk_homEdge_id hX.1 f

theorem globularClass_eq_id_of_equivalent {p : RoundPastingDiagram X}
    {f : X.Edge x y} (ep : Equivalent p (cellRound f.cell))
    (u : RoundPastingDiagram X) (hu : HasRoundType u.toPastingDiagram p p)
    (h : Equivalent u p.isRound.unit) : globularClass hX ep ep u hu = 𝟙 _ :=
  ((globularClass_eq_iff hX ep ep u p.isRound.unit hu (hasRoundType_unit p)).2 h).trans
    (globularClass_unit hX ep _)

end Globular

noncomputable def bipointedSuspensionPointIso :
    bipointedSuspension.obj (ball.{u} (atomSimplex 0)) ≅ Under.mk intervalBoundaryι.{u} := by
  refine bipointedSuspensionBallIso (atomSimplex 0) ≪≫
    (CategoryTheory.Under.isoMk (uliftYoneda.mapIso intervalSuspIso) ?_).symm
  change intervalBoundaryι ≫ uliftYoneda.map intervalSuspIso.hom =
    suspendedBallPoles (atomSimplex 0)
  have hface (α : Bool) :
      uliftYoneda.map (simplexHom (SimplexCategory.δ (cond α 0 1 : Fin 2)).toOrderHom) ≫
        uliftYoneda.map intervalSuspIso.hom =
      uliftYoneda.{u}.map (suspPole (atomSimplex 0) α) := by
    have h : toAtomPoint (atomSimplex 0) ≫ suspPole (atomSimplex 0) α =
        suspPole (atomSimplex 0) α :=
      (congrArg (· ≫ suspPole (atomSimplex 0) α)
        (Subsingleton.elim (toAtomPoint (atomSimplex 0)) (𝟙 atomPoint))).trans
          (Category.id_comp _)
    rw [← Functor.map_comp, face_comp_hom_eq, h]
    rfl
  have h₀ : intervalSource ≫ uliftYoneda.map intervalSuspIso.hom =
      uliftYoneda.{u}.map (suspPole (atomSimplex 0) false) := hface false
  have h₁ : intervalTarget ≫ uliftYoneda.map intervalSuspIso.hom =
      uliftYoneda.{u}.map (suspPole (atomSimplex 0) true) := hface true
  exact coprod.hom_ext (by simpa only [suspendedBallPoles, coprod.inl_desc_assoc,
    coprod.inl_desc] using h₀) (by simpa only [suspendedBallPoles, coprod.inr_desc_assoc,
    coprod.inr_desc] using h₁)

end Atoms.Diagrammatic
