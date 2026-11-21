import Atoms.Diagrammatic.KanComparison

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {X G : DiagSet.{u}}

def DiagSet.core (X : DiagSet.{u}) : Subfunctor X where
  obj U := {x | ∀ f : atomSimplex 1 ⟶ U.unop, IsEquivalence X (X.map f.op x)}
  map {U V} g x hx f := by
    have h := hx (f ≫ g.unop)
    rwa [op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply] at h

theorem DiagSet.mem_core_iff {U : Atom} (x : diagram X U) :
    x ∈ (DiagSet.core X).obj (op U) ↔
      ∀ f : atomSimplex 1 ⟶ U, IsEquivalence X (X.map f.op x) :=
  Iff.rfl

theorem DiagSet.range_le_core_iff {Z : DiagSet.{u}} (g : Z ⟶ X) :
    Subfunctor.range g ≤ DiagSet.core X ↔
      ∀ s : diagram Z (atomSimplex 1), IsEquivalence X (g.app (op (atomSimplex 1)) s) := by
  constructor
  · intro h s
    have hs := (DiagSet.mem_core_iff _).1 (h (op (atomSimplex 1)) ⟨s, rfl⟩) (𝟙 _)
    rwa [op_id, Functor.map_id_apply] at hs
  · rintro h ⟨U⟩ _ ⟨z, rfl⟩ f
    rw [← NatTrans.naturality_apply]
    exact h _

theorem DiagSet.mem_core_iff_isInclusionHom {U : Atom} (x : diagram X U) :
    x ∈ (DiagSet.core X).obj (op U) ↔
      ∀ (V : Atom) (i : V ⟶ U), IsInclusionHom i → V.dimension = 1 →
        IsEquivalence X (X.map i.op x) := by
  constructor
  · intro hx V i _ hV
    obtain ⟨φ⟩ := (nonempty_iso_atomGlobe_of_dimension_eq_one hV).map
      fun i => i.symm ≪≫ atomSimplexOneIsoGlobe.symm
    have h := hx (φ.inv ≫ i)
    rw [op_comp, Functor.map_comp_apply] at h
    exact (isEquivalence_map_iso_iff φ.symm _).1 h
  · intro h f
    obtain ⟨W, p, i, hp, hi, rfl⟩ := exists_collapse_inclusion_factorization f
    rw [op_comp, Functor.map_comp_apply]
    by_cases hiso : IsIso p
    · have hW : W.dimension = 1 :=
        (Atom.dimension_eq_of_iso (asIso p)).symm.trans (dimension_atomSimplex 1)
      exact (isEquivalence_map_iso_iff (asIso p) _).2 (h W i hi hW)
    · exact degenerate_isEquivalence X _ ⟨W, p, X.map i.op x, hp, hiso, rfl⟩

theorem DiagSet.mem_core_iff_globe {U : Atom} (x : diagram X U) :
    x ∈ (DiagSet.core X).obj (op U) ↔
      ∀ i : atomGlobe 1 ⟶ U, IsEquivalence X (X.map i.op x) := by
  constructor
  · intro hx i
    have h := hx (atomSimplexOneIsoGlobe.hom ≫ i)
    rw [op_comp, Functor.map_comp_apply] at h
    exact (isEquivalence_map_iso_iff atomSimplexOneIsoGlobe _).1 h
  · intro h
    apply (DiagSet.mem_core_iff_isInclusionHom x).2
    intro V i _ hV
    obtain ⟨φ⟩ := nonempty_iso_atomGlobe_of_dimension_eq_one hV
    have hi := h (φ.hom ≫ i)
    rw [op_comp, Functor.map_comp_apply] at hi
    exact (isEquivalence_map_iso_iff φ _).1 hi

theorem DiagSet.mem_core_of_dimension_eq_zero {U : Atom} (x : diagram X U)
    (hU : U.dimension = 0) : x ∈ (DiagSet.core X).obj (op U) :=
  (DiagSet.mem_core_iff_isInclusionHom x).2 fun V i hi hV => by
    have := dimension_le_of_isInclusionHom i hi
    omega

theorem DiagSet.mem_core_iff_of_dimension_eq_one {U : Atom} (x : diagram X U)
    (hU : U.dimension = 1) : x ∈ (DiagSet.core X).obj (op U) ↔ IsEquivalence X x := by
  rw [DiagSet.mem_core_iff_isInclusionHom]
  constructor
  · intro h
    have hx := h U (𝟙 U) (fun _ _ hab => hab) hU
    rwa [op_id, Functor.map_id_apply] at hx
  · intro hx V i hi hV
    have := isIso_of_isInclusionHom_of_dimension_eq i hi (hV.trans hU.symm)
    exact (isEquivalence_map_iso_iff (asIso i) x).2 hx

section Range

open PastingDiagram

private theorem mem_range_of_within {a m : PastingDiagram X} (w : Within a m) {T : Atom}
    (g : atomToRDCpx.obj T ⟶ m.shape.rdc)
    (hg : ∀ t, ConcreteCategory.hom g.hom t ∈ w.image) :
    m.map.app (op T) ⟨g⟩ ∈ Set.range (a.map.app (op T)) := by
  obtain ⟨e, he⟩ := RDCpx.exists_iso_restrict (U := a.shape.rdc) (R := m.shape.rdc) w.emb
  refine ⟨⟨RDCpx.codRestrict g (OGP.map w.emb ⊤) hg ≫ e.inv⟩, ?_⟩
  rw [← w.comm, realize_map_comp_app, Category.assoc, ← he, Iso.inv_hom_id_assoc]
  exact congrArg (fun k => m.map.app (op T) ⟨k⟩) (RDCpx.codRestrict_restrictIncl g _ hg)

private theorem range_le_sup_of_within {a b m : PastingDiagram X} (w₁ : Within a m)
    (w₂ : Within b m) (h : w₁.image ⊔ w₂.image = ⊤) :
    Subfunctor.range m.map ≤ Subfunctor.range a.map ⊔ Subfunctor.range b.map := by
  rintro ⟨T⟩ _ ⟨⟨g⟩, rfl⟩
  have ht : ConcreteCategory.hom g.hom T.top ∈ w₁.image ⊔ w₂.image := h ▸ LowerSet.mem_top
  rcases LowerSet.mem_sup_iff.1 ht with h₁ | h₂
  · exact Or.inl (mem_range_of_within w₁ g (apply_mem_of_apply_top_mem g h₁))
  · exact Or.inr (mem_range_of_within w₂ g (apply_mem_of_apply_top_mem g h₂))

private theorem range_le_of_equiv {u v : PastingDiagram X} (h : u.Equiv v) :
    Subfunctor.range u.map ≤ Subfunctor.range v.map := by
  rw [← h.map_comm]
  exact Subfunctor.range_comp_le _ _

private theorem range_boundary_le (u : PastingDiagram X) (k : ℕ) (α : Bool) :
    Subfunctor.range (u.boundary k α).map ≤ Subfunctor.range u.map :=
  Subfunctor.range_comp_le _ _

private theorem range_unit_le (u : PastingDiagram X) :
    Subfunctor.range u.unit.map ≤ Subfunctor.range u.map :=
  Subfunctor.range_comp_le _ _

private theorem range_paste_le (u v : PastingDiagram X) (k : ℕ) (h : u.Pastable v k) :
    Subfunctor.range (u.paste v k h).map ≤ Subfunctor.range u.map ⊔ Subfunctor.range v.map :=
  range_le_sup_of_within (Within.pasteInl u v k h) (Within.pasteInr u v k h)
    (Within.isPastingIn_paste u v k h).sup_eq

private theorem range_mapTo_ι_le (u : PastingDiagram (DiagSet.core X).toFunctor) :
    Subfunctor.range (u.mapTo (DiagSet.core X).ι).map ≤ DiagSet.core X :=
  (Subfunctor.range_comp_le _ _).trans (Subfunctor.range_ι _).le

private theorem range_ofCell_le_core {U : Atom} {x : diagram X U}
    (hx : x ∈ (DiagSet.core X).obj (op U)) :
    Subfunctor.range (ofCell x).map ≤ DiagSet.core X := by
  refine (Subfunctor.range_comp_le _ _).trans ?_
  rintro ⟨T⟩ _ ⟨⟨f⟩, rfl⟩
  exact (DiagSet.core X).map f.op hx

end Range

section Cells

open PastingDiagram

private theorem grade_atomSimplex_one_top : grade ℕ (atomSimplex 1).top = 1 := by
  rw [← Atom.dimension_eq, dimension_atomSimplex]

theorem DiagSet.mem_core_of_range_boundary_le {U : Atom} (x : diagram X U) (hU : 2 ≤ U.dimension)
    (h : ∀ α, Subfunctor.range ((ofCell x).boundary (U.dimension - 1) α).map ≤ DiagSet.core X) :
    x ∈ (DiagSet.core X).obj (op U) := by
  intro f
  have hgr : grade ℕ (f (atomSimplex 1).top) ≤ 1 :=
    ((Atom.isMap f).grade_le _).trans grade_atomSimplex_one_top.le
  have hne : f (atomSimplex 1).top ≠ U.top := fun he => by
    have hd := U.dimension_eq
    rw [← he] at hd
    omega
  have hk : Order.krullDim (⊤ : LowerSet U.ogp) = ((U.dimension - 1 : ℕ) : WithBot ℕ∞) + 1 :=
    U.toMoleculeShape.krullDim_top_eq (by omega)
  obtain ⟨α, hα⟩ : ∃ α, f (atomSimplex 1).top ∈ U.ogp.boundary ⊤ (U.dimension - 1) α := by
    rcases LowerSet.mem_sup_iff.1 ((U.mem_bdryFull_top_iff _).2 hne) with h₀ | h₁
    · exact ⟨false, bdry_eq_boundary hk false ▸ h₀⟩
    · exact ⟨true, bdry_eq_boundary hk true ▸ h₁⟩
  have ht : ConcreteCategory.hom (atomToRDCpx.map f).hom (atomSimplex 1).top ∈
      (Within.boundary (ofCell x) (U.dimension - 1) α).image := by
    rw [Within.image_boundary]
    exact hα
  obtain ⟨s, hs⟩ := mem_range_of_within (Within.boundary (ofCell x) (U.dimension - 1) α)
    (atomToRDCpx.map f)
    (apply_mem_of_apply_top_mem (T := atomSimplex 1) (P := (ofCell x).shape.rdc)
      (S := (Within.boundary (ofCell x) (U.dimension - 1) α).image) (atomToRDCpx.map f) ht)
  rw [← ofCell_map_app_map, ← hs]
  exact (DiagSet.range_le_core_iff _).1 (h α) s

theorem PastingDiagram.range_le_core_iff (u : PastingDiagram X) :
    Subfunctor.range u.map ≤ DiagSet.core X ↔
      ∀ x : u.shape.ogp, grade ℕ x = 1 → IsEquivalence X (u.cellAt x) := by
  constructor
  · intro h x hx
    exact (DiagSet.mem_core_iff_of_dimension_eq_one (u.cellAt x)
      ((dimension_principalAtomRDC u.shape.rdc x).trans hx)).1
        (h (op _) ⟨⟨principalInclusionRDC u.shape.rdc x⟩, rfl⟩)
  · intro h
    rw [DiagSet.range_le_core_iff]
    rintro ⟨g⟩
    let t := ConcreteCategory.hom g.hom (atomSimplex 1).top
    have hq := principalLiftRDC_comp_principalInclusionRDC u.shape.rdc t g
      (hom_apply_mem_closure_apply_top g)
    have hgr : grade ℕ t ≤ 1 :=
      ((ConcreteCategory.hom g.hom).isMap.grade_le _).trans grade_atomSimplex_one_top.le
    have hc : u.cellAt t ∈ (DiagSet.core X).obj (op _) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hgr with h0 | h1
      · exact DiagSet.mem_core_of_dimension_eq_zero _
          ((dimension_principalAtomRDC u.shape.rdc t).trans h0)
      · exact (DiagSet.mem_core_iff_of_dimension_eq_one _
          ((dimension_principalAtomRDC u.shape.rdc t).trans h1)).2 (h t h1)
    have hval : u.map.app (op (atomSimplex 1)) ⟨g⟩ =
        X.map (principalLiftRDC u.shape.rdc t g (hom_apply_mem_closure_apply_top g)).op
          (u.cellAt t) := by
      refine Eq.trans ?_ (NatTrans.naturality_apply u.map
        (principalLiftRDC u.shape.rdc t g (hom_apply_mem_closure_apply_top g)).op
        (⟨principalInclusionRDC u.shape.rdc t⟩ : (realize.obj u.shape.rdc).obj (op _)))
      exact congrArg (fun k => u.map.app (op (atomSimplex 1)) ⟨k⟩) hq.symm
    rw [hval]
    have hm := (DiagSet.core X).map
      (principalLiftRDC u.shape.rdc t g (hom_apply_mem_closure_apply_top g)).op hc (𝟙 _)
    rwa [op_id, Functor.map_id_apply] at hm

end Cells

section Cellular

open PastingDiagram

private theorem equivalent_composite (α : Bool) {e h h' : RoundPastingDiagram X}
    (hh : Equivalent h h') (hd : h.dim = e.dim) {n : ℕ}
    (hp : (cond α h.toPastingDiagram e.toPastingDiagram).Pastable
      (cond α e.toPastingDiagram h.toPastingDiagram) n)
    (hp' : (cond α h'.toPastingDiagram e.toPastingDiagram).Pastable
      (cond α e.toPastingDiagram h'.toPastingDiagram) n)
    (hr : ((cond α h.toPastingDiagram e.toPastingDiagram).paste
      (cond α e.toPastingDiagram h.toPastingDiagram) n hp).IsRound)
    (hr' : ((cond α h'.toPastingDiagram e.toPastingDiagram).paste
      (cond α e.toPastingDiagram h'.toPastingDiagram) n hp').IsRound) :
    Equivalent ⟨_, hr⟩ ⟨_, hr'⟩ := by
  cases α
  · exact equivalent_paste_right hh rfl hd.symm hp hp' hr hr'
  · exact equivalent_paste_left hh hd hp hp' hr hr'

theorem exists_cellular_biInvData (hX : HasWeakComposites X) {e : RoundPastingDiagram X}
    (he : e ∈ equivalences X) :
    ∃ d : BiInvData (equivalences X) e,
      (∀ α, ∃ (U : Atom) (c : diagram X U), d.inverse α = cellRound c) ∧
      (∀ α, ∃ (U : Atom) (c : diagram X U), d.invertor α = cellRound c) := by
  let D := ((mem_equivalences_iff e).1 he).data
  have hpos := D.dim_pos
  choose c hc using fun α => hX (D.inverse α)
  have hdc (α : Bool) : (cellRound (c α)).dim = e.dim :=
    (hc α).data.dim_eq.symm.trans (D.dim_inverse α)
  have hb (α γ : Bool) : ((cellRound (c α)).boundary (e.dim - 1) γ).Equiv
      (e.boundary (e.dim - 1) (!γ)) :=
    ((hc α).equiv_boundary (by rw [D.dim_inverse α]; omega) γ).symm.trans
      (D.equiv_boundary_inverse α γ)
  have hp (α : Bool) : (cond α (cellRound (c α)).toPastingDiagram e.toPastingDiagram).Pastable
      (cond α e.toPastingDiagram (cellRound (c α)).toPastingDiagram) (e.dim - 1) :=
    Pastable.of_side α (hb α α) (by rw [hdc]; omega) (by omega)
  have hr (α : Bool) : ((cond α (D.inverse α).toPastingDiagram e.toPastingDiagram).paste
      (cond α e.toPastingDiagram (D.inverse α).toPastingDiagram) (e.dim - 1)
        (D.pastable α)).IsRound :=
    isRound_paste_of_round α (D.pastable α) e.isRound (by omega)
      (by rw [D.dim_inverse]; omega)
  have hr' (α : Bool) : ((cond α (cellRound (c α)).toPastingDiagram e.toPastingDiagram).paste
      (cond α e.toPastingDiagram (cellRound (c α)).toPastingDiagram) (e.dim - 1)
        (hp α)).IsRound :=
    isRound_paste_of_round α (hp α) e.isRound (by omega) (by rw [hdc]; omega)
  have hw (α : Bool) : ∃ (V : Atom) (w : diagram X V), IsEquivalence X w ∧
      V.dimension = e.dim + 1 ∧
      ((cellRound w).boundary e.dim α).Equiv
        ((cond α (cellRound (c α)).toPastingDiagram e.toPastingDiagram).paste
          (cond α e.toPastingDiagram (cellRound (c α)).toPastingDiagram) (e.dim - 1) (hp α)) ∧
      ((cellRound w).boundary e.dim (!α)).Equiv (e.boundary (e.dim - 1) α).unit := by
    have hq := equivalent_trans
      (equivalent_symm (equivalent_composite α (hc α) (D.dim_inverse α) (D.pastable α) (hp α)
        (hr α) (hr' α)))
      (D.equivalent_invertor α (hr α))
    obtain ⟨V, w, hw, hdV, h₁, h₂⟩ := exists_equivalence_cell_side hX α _ _ hq
    have hdim : (⟨_, hr' α⟩ : RoundPastingDiagram X).dim = e.dim := by
      rw [dim_paste_cond, hdc, max_self]
    rw [hdim] at hdV h₁ h₂
    exact ⟨V, w, hw, hdV, h₁, h₂⟩
  choose V w hw hdV h₁ h₂ using hw
  exact ⟨{ dim_pos := hpos
           inverse := fun α => cellRound (c α)
           invertor := fun α => cellRound (w α)
           invertor_mem := hw
           dim_inverse := hdc
           dim_invertor := hdV
           equiv_boundary_inverse := hb
           pastable := hp
           boundary_invertor_composite := h₁
           boundary_invertor_unit := h₂ },
    fun α => ⟨_, c α, rfl⟩, fun α => ⟨_, w α, rfl⟩⟩

end Cellular

section Reflection

open PastingDiagram

private theorem mapTo_cellRound_lift {U : Atom} {c : diagram X U}
    (hc : c ∈ (DiagSet.core X).obj (op U)) :
    (cellRound (X := (DiagSet.core X).toFunctor) ⟨c, hc⟩).toPastingDiagram.mapTo
      (DiagSet.core X).ι = (cellRound c).toPastingDiagram :=
  (PastingDiagram.ofCell_app (DiagSet.core X).ι
    (⟨c, hc⟩ : diagram (DiagSet.core X).toFunctor U)).symm

private theorem mem_core_of_cases {U : Atom} {c : diagram X U} (hpos : 0 < U.dimension)
    (h₁ : U.dimension = 1 → IsEquivalence X c)
    (h₂ : 2 ≤ U.dimension → ∀ α,
      Subfunctor.range ((ofCell c).boundary (U.dimension - 1) α).map ≤ DiagSet.core X) :
    c ∈ (DiagSet.core X).obj (op U) := by
  rcases Nat.lt_or_ge U.dimension 2 with hU | hU
  · have hU1 : U.dimension = 1 := by omega
    exact (DiagSet.mem_core_iff_of_dimension_eq_one c hU1).2 (h₁ hU1)
  · exact DiagSet.mem_core_of_range_boundary_le c hU (h₂ hU)

private theorem nonempty_biInvData_core (hX : HasWeakComposites X)
    {e : RoundPastingDiagram (DiagSet.core X).toFunctor}
    (he : (⟨e.toPastingDiagram.mapTo (DiagSet.core X).ι, e.isRound⟩ : RoundPastingDiagram X) ∈
      equivalences X) :
    Nonempty (BiInvData {d : RoundPastingDiagram (DiagSet.core X).toFunctor |
      (⟨d.toPastingDiagram.mapTo (DiagSet.core X).ι, d.isRound⟩ : RoundPastingDiagram X) ∈
        equivalences X} e) := by
  let ι := (DiagSet.core X).ι
  let e' : RoundPastingDiagram X := ⟨e.toPastingDiagram.mapTo ι, e.isRound⟩
  obtain ⟨d, hinv, hinvt⟩ := exists_cellular_biInvData hX he
  choose U c hc using hinv
  choose V w hw using hinvt
  have hpos : 0 < e.dim := d.dim_pos
  have he'r : Subfunctor.range e'.map ≤ DiagSet.core X := range_mapTo_ι_le e.toPastingDiagram
  have hdU (α : Bool) : (U α).dimension = e.dim := (congrArg (·.dim) (hc α)).symm.trans
    (d.dim_inverse α)
  have hdV (α : Bool) : (V α).dimension = e.dim + 1 := (congrArg (·.dim) (hw α)).symm.trans
    (d.dim_invertor α)
  have hcm (α : Bool) : c α ∈ (DiagSet.core X).obj (op (U α)) := by
    refine mem_core_of_cases (by rw [hdU α]; exact hpos) (fun _ => ?_) (fun _ γ => ?_)
    · change cellRound (c α) ∈ equivalences X
      rw [← hc α]
      cases α
      exacts [d.leftInverse_mem he, d.rightInverse_mem he]
    · have hb : ((cellRound (c α)).boundary ((U α).dimension - 1) γ).Equiv
          (e'.boundary (e.dim - 1) (!γ)) := by
        rw [← hc α, hdU α]
        exact d.equiv_boundary_inverse α γ
      exact (range_le_of_equiv hb).trans ((range_boundary_le _ _ _).trans he'r)
  have hir (α : Bool) : Subfunctor.range (d.inverse α).map ≤ DiagSet.core X := by
    rw [hc α]
    exact range_ofCell_le_core (hcm α)
  have hwm (α : Bool) : w α ∈ (DiagSet.core X).obj (op (V α)) := by
    refine mem_core_of_cases (by rw [hdV α]; omega) (fun h => by rw [hdV α] at h; omega)
      (fun _ γ => ?_)
    rw [hdV α, Nat.add_sub_cancel]
    obtain rfl | rfl : γ = α ∨ γ = !α := by cases γ <;> cases α <;> simp
    · have hb : ((cellRound (w γ)).boundary e.dim γ).Equiv
          ((cond γ (d.inverse γ).toPastingDiagram e'.toPastingDiagram).paste
            (cond γ e'.toPastingDiagram (d.inverse γ).toPastingDiagram) (e.dim - 1)
              (d.pastable γ)) := by
        rw [← hw γ]
        exact d.boundary_invertor_composite γ
      refine (range_le_of_equiv hb).trans ((range_paste_le _ _ _ _).trans (sup_le ?_ ?_)) <;>
        cases γ
      exacts [he'r, hir _, hir _, he'r]
    · have hb : ((cellRound (w α)).boundary e.dim (!α)).Equiv
          (e'.boundary (e.dim - 1) α).unit := by
        rw [← hw α]
        exact d.boundary_invertor_unit α
      exact (range_le_of_equiv hb).trans
        ((range_unit_le _).trans ((range_boundary_le _ _ _).trans he'r))
  let c' (α : Bool) : RoundPastingDiagram (DiagSet.core X).toFunctor := cellRound ⟨c α, hcm α⟩
  let w' (α : Bool) : RoundPastingDiagram (DiagSet.core X).toFunctor := cellRound ⟨w α, hwm α⟩
  have hc' (α : Bool) : (c' α).toPastingDiagram.mapTo ι = (d.inverse α).toPastingDiagram :=
    (mapTo_cellRound_lift (hcm α)).trans (congrArg (·.toPastingDiagram) (hc α)).symm
  have hw' (α : Bool) : (w' α).toPastingDiagram.mapTo ι = (d.invertor α).toPastingDiagram :=
    (mapTo_cellRound_lift (hwm α)).trans (congrArg (·.toPastingDiagram) (hw α)).symm
  have hcond (α : Bool) (a b : PastingDiagram (DiagSet.core X).toFunctor) :
      (cond α a b).mapTo ι = cond α (a.mapTo ι) (b.mapTo ι) := by
    cases α <;> rfl
  have hpS (α : Bool) : (cond α (c' α).toPastingDiagram e.toPastingDiagram).Pastable
      (cond α e.toPastingDiagram (c' α).toPastingDiagram) (e.dim - 1) := by
    refine Pastable.of_mapTo ι ?_
    rw [hcond, hcond, hc' α]
    exact d.pastable α
  refine ⟨{ dim_pos := hpos
            inverse := c'
            invertor := w'
            invertor_mem := fun α => ?_
            dim_inverse := fun α => (hdU α)
            dim_invertor := fun α => (hdV α)
            equiv_boundary_inverse := fun α γ => ?_
            pastable := hpS
            boundary_invertor_composite := fun α => ?_
            boundary_invertor_unit := fun α => ?_ }⟩
  · change (⟨(w' α).toPastingDiagram.mapTo ι, (w' α).isRound⟩ : RoundPastingDiagram X) ∈
      equivalences X
    rw [show (⟨(w' α).toPastingDiagram.mapTo ι, (w' α).isRound⟩ : RoundPastingDiagram X) =
        d.invertor α from
      RoundPastingDiagram.ext (hw' α)]
    exact d.invertor_mem α
  · refine Equiv.of_mapTo ι ?_
    rw [← boundary_mapTo, ← boundary_mapTo, hc' α]
    exact d.equiv_boundary_inverse α γ
  · refine Equiv.of_mapTo ι ?_
    rw [← boundary_mapTo, hw' α]
    have hu : (cond α (d.inverse α).toPastingDiagram e'.toPastingDiagram).Equiv
        ((cond α (c' α).toPastingDiagram e.toPastingDiagram).mapTo ι) := by
      rw [hcond, hc' α]
    have hv : (cond α e'.toPastingDiagram (d.inverse α).toPastingDiagram).Equiv
        ((cond α e.toPastingDiagram (c' α).toPastingDiagram).mapTo ι) := by
      rw [hcond, hc' α]
    exact (d.boundary_invertor_composite α).trans
      ((Equiv.paste hu hv _ ((hpS α).mapTo ι)).trans
        (paste_mapTo _ _ _ (hpS α) ι ((hpS α).mapTo ι)).symm)
  · refine Equiv.of_mapTo ι ?_
    rw [← boundary_mapTo, hw' α, ← unit_mapTo, ← boundary_mapTo]
    exact d.boundary_invertor_unit α

theorem mem_equivalences_core_iff (hX : HasWeakComposites X)
    (e : RoundPastingDiagram (DiagSet.core X).toFunctor) :
    e ∈ equivalences (DiagSet.core X).toFunctor ↔
      (⟨e.toPastingDiagram.mapTo (DiagSet.core X).ι, e.isRound⟩ : RoundPastingDiagram X) ∈
        equivalences X :=
  ⟨mapTo_mem_equivalences _, fun he => subset_equivalences
    (A := {d : RoundPastingDiagram (DiagSet.core X).toFunctor |
      (⟨d.toPastingDiagram.mapTo (DiagSet.core X).ι, d.isRound⟩ : RoundPastingDiagram X) ∈
        equivalences X})
    (fun _ hd => (nonempty_biInvData_core hX hd).some.witness) he⟩

theorem isEquivalence_core_iff (hX : HasWeakComposites X) {U : Atom}
    (x : diagram (DiagSet.core X).toFunctor U) :
    IsEquivalence (DiagSet.core X).toFunctor x ↔
      IsEquivalence X ((DiagSet.core X).ι.app (op U) x) := by
  have hc : cellRound ((DiagSet.core X).ι.app (op U) x) =
      ⟨(cellRound x).toPastingDiagram.mapTo (DiagSet.core X).ι, (cellRound x).isRound⟩ :=
    RoundPastingDiagram.ext (PastingDiagram.ofCell_app _ x)
  change cellRound x ∈ _ ↔ cellRound ((DiagSet.core X).ι.app (op U) x) ∈ _
  rw [hc]
  exact mem_equivalences_core_iff hX _

end Reflection

section InftyZero

open PastingDiagram HomotopicalAlgebra

private theorem isEquivalence_ι_app (hX : IsInftyCategory 1 X) {U : Atom}
    (x : diagram (DiagSet.core X).toFunctor U) (hU : 0 < U.dimension) :
    IsEquivalence X ((DiagSet.core X).ι.app (op U) x) := by
  rcases Nat.lt_or_ge U.dimension 2 with h | h
  · exact (DiagSet.mem_core_iff_of_dimension_eq_one x.1 (by omega)).1 x.2
  · exact hX.2 U _ (by exact_mod_cast (show 1 < U.dimension by omega))

private theorem hasWeakComposites_core (hX : IsInftyCategory 1 X) :
    HasWeakComposites (DiagSet.core X).toFunctor := by
  rw [hasWeakComposites_iff_positive]
  intro u hu
  let u' : RoundPastingDiagram X := ⟨u.toPastingDiagram.mapTo (DiagSet.core X).ι, u.isRound⟩
  have hu'r : Subfunctor.range u'.map ≤ DiagSet.core X := range_mapTo_ι_le u.toPastingDiagram
  obtain ⟨c, hc⟩ := (hasWeakComposites_iff_positive X).1 hX.1 u' hu
  have hdc : (mergerAtom u'.roundShape hu).dimension = u.dim := hc.data.dim_eq.symm
  have hcm : c ∈ (DiagSet.core X).obj (op _) := by
    refine mem_core_of_cases (by rw [hdc]; exact hu) (fun h1 => ?_)
      (fun _ γ => ?_)
    · have hd : u'.dim = 1 := hdc.symm.trans h1
      have hu' : u' ∈ equivalences X := mem_equivalences_of_forall_cellAt u' (by omega)
        fun t ht => (u'.range_le_core_iff).1 hu'r t (ht.trans hd)
      exact (mem_equivalences_iff_of_equivalent hc).1 hu'
    · have hb := hc.equiv_boundary (k := (mergerAtom u'.roundShape hu).dimension - 1)
        (by change _ < u.dim; omega) γ
      exact (range_le_of_equiv hb.symm).trans ((range_boundary_le _ _ _).trans hu'r)
  obtain ⟨V, w, hw, hdV, hs, ht⟩ := exists_equivalence_cell_side hX.1 false u' (cellRound c) hc
  have hdV' : V.dimension = u.dim + 1 := hdV
  have hwm : w ∈ (DiagSet.core X).obj (op V) := by
    refine DiagSet.mem_core_of_range_boundary_le w (by omega) fun γ => ?_
    rw [hdV, Nat.add_sub_cancel]
    cases γ
    · exact (range_le_of_equiv hs).trans hu'r
    · exact (range_le_of_equiv ht).trans (range_ofCell_le_core hcm)
  refine ⟨(⟨c, hcm⟩ : diagram (DiagSet.core X).toFunctor (mergerAtom u'.roundShape hu)),
    EquivalenceData.equivalent
    { dim_eq := hc.data.dim_eq
      equivalence := cellRound (⟨w, hwm⟩ : diagram (DiagSet.core X).toFunctor V)
      mem := (mem_equivalences_core_iff hX.1 _).2 ?_
      dim_equivalence := hdV
      source := Equiv.of_mapTo (DiagSet.core X).ι ?_
      target := Equiv.of_mapTo (DiagSet.core X).ι ?_ }⟩
  · rw [show (⟨(cellRound (⟨w, hwm⟩ : diagram (DiagSet.core X).toFunctor V)).toPastingDiagram.mapTo
        (DiagSet.core X).ι, (cellRound _).isRound⟩ : RoundPastingDiagram X) = cellRound w from
      RoundPastingDiagram.ext (mapTo_cellRound_lift hwm)]
    exact hw
  · rw [← boundary_mapTo, mapTo_cellRound_lift hwm]
    exact hs
  · rw [← boundary_mapTo, mapTo_cellRound_lift hwm]
    have h := mapTo_cellRound_lift hcm
    exact ht.trans (h ▸ PastingDiagram.Equiv.refl _)

theorem isInftyCategory_core (hX : IsInftyCategory 1 X) :
    IsInftyCategory 0 (DiagSet.core X).toFunctor :=
  ⟨hasWeakComposites_core hX, fun _ x hU =>
    (isEquivalence_core_iff hX.1 x).2 (isEquivalence_ι_app hX x (Nat.cast_pos.1 hU))⟩

theorem isFibrant_core (hX : IsInftyCategory 1 X) :
    IsFibrant ((DiagSet.toInfty 0).obj (DiagSet.core X).toFunctor) :=
  (isFibrant_infty_iff 0 _).2 (isInftyCategory_core hX)

end InftyZero

theorem DiagSet.range_le_core (hG : IsInftyCategory 0 G) (f : G ⟶ X) :
    Subfunctor.range f ≤ DiagSet.core X :=
  (DiagSet.range_le_core_iff f).2 fun s =>
    (hG.2 _ s (by rw [dimension_atomSimplex]; exact_mod_cast Nat.one_pos)).map f

def DiagSet.coreLiftEquiv (hG : IsInftyCategory 0 G) :
    (G ⟶ (DiagSet.core X).toFunctor) ≃ (G ⟶ X) where
  toFun g := g ≫ (DiagSet.core X).ι
  invFun f := Subfunctor.lift f (DiagSet.range_le_core hG f)
  left_inv _ := (cancel_mono (DiagSet.core X).ι).1 (Subfunctor.lift_ι _ _)
  right_inv _ := Subfunctor.lift_ι _ _

@[simp]
theorem DiagSet.coreLiftEquiv_apply (hG : IsInftyCategory 0 G)
    (g : G ⟶ (DiagSet.core X).toFunctor) :
    DiagSet.coreLiftEquiv hG g = g ≫ (DiagSet.core X).ι :=
  rfl

def DiagSet.coreMap {X Y : DiagSet.{u}} (f : X ⟶ Y) :
    (DiagSet.core X).toFunctor ⟶ (DiagSet.core Y).toFunctor :=
  Subfunctor.lift ((DiagSet.core X).ι ≫ f) ((DiagSet.range_le_core_iff _).2 fun s => by
    have hs := s.2 (𝟙 _)
    rw [op_id, Functor.map_id_apply] at hs
    exact hs.map f)

@[reassoc (attr := simp)]
theorem DiagSet.coreMap_ι {X Y : DiagSet.{u}} (f : X ⟶ Y) :
    DiagSet.coreMap f ≫ (DiagSet.core Y).ι = (DiagSet.core X).ι ≫ f :=
  Subfunctor.lift_ι _ _

def DiagSet.coreFunctor : DiagSet.{u} ⥤ DiagSet.{u} where
  obj X := (DiagSet.core X).toFunctor
  map f := DiagSet.coreMap f
  map_id X := (cancel_mono (DiagSet.core X).ι).1 (by
    rw [DiagSet.coreMap_ι, Category.id_comp, Category.comp_id])
  map_comp _ _ := (cancel_mono (DiagSet.core _).ι).1 (by
    rw [DiagSet.coreMap_ι, Category.assoc, DiagSet.coreMap_ι, DiagSet.coreMap_ι_assoc])

theorem DiagSet.core_eq_top_iff (hX : IsInftyCategory 1 X) :
    DiagSet.core X = ⊤ ↔ IsInftyCategory 0 X := by
  constructor
  · intro h
    refine ⟨hX.1, fun U x hU => ?_⟩
    have hx : x ∈ (DiagSet.core X).obj (op U) := by
      rw [h]
      trivial
    have hpos := Nat.cast_pos.1 hU
    rcases Nat.lt_or_ge U.dimension 2 with h2 | h2
    · exact (DiagSet.mem_core_iff_of_dimension_eq_one x (by omega)).1 hx
    · exact hX.2 U x (by exact_mod_cast (show 1 < U.dimension by omega))
  · intro h0
    exact top_le_iff.1 ((Subfunctor.range_id X).symm.le.trans (DiagSet.range_le_core h0 (𝟙 X)))

section Comparison

open Simplicial

private theorem isEquivalence_edge_iff (hX : IsInftyCategory 1 X)
    {x y : (DiagSet.toSSet.obj X) _⦋0⦌} (e : SSet.Edge x y) :
    IsEquivalence X e.edge ↔ IsIso (SSet.Truncated.HomotopyCategory.homMk e) := by
  have : (DiagSet.toSSet.obj X).Quasicategory :=
    quasicategory_toSSet_obj X ((isFibrant_infty_iff 1 X).2 hX)
  exact (Iff.intro (nonempty_invStruct_of_isEquivalence hX e)
    (isEquivalence_of_invStruct hX e)).trans (SSet.isIso_homMk_iff e).symm

private theorem mem_core_toSSet_iff (hX : IsInftyCategory 1 X)
    (n : SimplexCategoryᵒᵖ) (x : (DiagSet.toSSet.obj X).obj n) :
    x ∈ (DiagSet.core X).obj (simplexFunctor.op.obj n) ↔
      x ∈ (DiagSet.toSSet.obj X).core.obj n := by
  constructor
  · intro hx f
    exact (isEquivalence_edge_iff hX (SSet.Edge.mk' _)).1 (hx (simplexFunctor.map f))
  · intro hx f
    obtain ⟨g, rfl⟩ := simplexFunctor.map_surjective f
    exact (isEquivalence_edge_iff hX (SSet.Edge.mk' _)).2 (hx g)

def DiagSet.toSSetCoreIso (hX : IsInftyCategory 1 X) :
    DiagSet.toSSet.obj (DiagSet.core X).toFunctor ≅ ((DiagSet.toSSet.obj X).core : SSet.{u}) :=
  NatIso.ofComponents (fun n => Equiv.toIso
    { toFun := fun x => ⟨x.val, (mem_core_toSSet_iff hX n x.val).1 x.property⟩
      invFun := fun x => ⟨x.val, (mem_core_toSSet_iff hX n x.val).2 x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) (by intros; rfl)

theorem kanComplex_toSSet_obj_core (hX : IsInftyCategory 1 X) :
    (DiagSet.toSSet.obj (DiagSet.core X).toFunctor).KanComplex :=
  kanComplex_toSSet_obj (isInftyCategory_core hX)

end Comparison

end Atoms.Diagrammatic
