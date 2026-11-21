import Atoms.Molecule.Construction.JoinInclusion
import Atoms.Molecule.RegularComplex.Comap

universe u v

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

open SuspCarrier

section Suspension

variable {P Q : OGP.{u}}

theorem lowerPreimage_susp {c : P → Q} (hc : Monotone c) (V : LowerSet Q) :
    lowerPreimage (monotone_suspMap hc) V.susp = (lowerPreimage hc V).susp :=
  SetLike.ext fun w => by
    cases w with
    | pole α => exact iff_of_true (pole_mem_susp V α) (pole_mem_susp _ α)
    | susp x =>
      have h := (susp_mem_susp (V := lowerPreimage hc V) (x := x)).symm
      exact (susp_mem_susp (V := V) (x := c x)).trans h

theorem lowerPreimage_Iic_pole {c : P → Q} (hc : Monotone c) (β : Bool) :
    lowerPreimage (monotone_suspMap hc) (.Iic (pole β)) = .Iic (pole β) :=
  SetLike.ext fun w => by
    cases w with
    | pole α => exact Iff.rfl
    | susp x => exact iff_of_false (not_susp_le_pole (c x) β) (not_susp_le_pole x β)

theorem IsComap.suspMap {c : P → Q} (hc : IsComap c) : IsComap (suspMap c) where
  monotone := monotone_suspMap hc.monotone
  isMoleculeIn_Iic y := by
    cases y with
    | pole β =>
      rw [lowerPreimage_Iic_pole hc.monotone]
      exact .point _ (isMin_pole β)
    | susp y =>
      rw [← susp_Iic, lowerPreimage_susp hc.monotone]
      exact isMoleculeIn_susp (hc.isMoleculeIn_Iic y)
  boundary_Iic y n α := by
    cases y with
    | pole β =>
      have h0 (R : OGP.{u}) : krullDim (LowerSet.Iic (pole β : suspension R)) ≤ n := by
        rw [LowerSet.krullDim_Iic, grade_pole]
        exact_mod_cast Nat.zero_le n
      rw [boundary_eq_self (h0 Q), lowerPreimage_Iic_pole hc.monotone, boundary_eq_self (h0 P)]
    | susp y =>
      have hm := hc.isMoleculeIn_Iic y
      rw [← susp_Iic, lowerPreimage_susp hc.monotone]
      cases n with
      | zero =>
        rw [boundary_susp_zero ⟨y, le_rfl⟩ α, lowerPreimage_Iic_pole hc.monotone,
          boundary_susp_zero hm.nonempty α]
      | succ m =>
        have hne := (hm.boundary m α).nonempty
        rw [← hc.boundary_Iic] at hne
        rw [boundary_susp_succ (hne.image c |>.mono (image_preimage_subset c _)),
          lowerPreimage_susp hc.monotone, hc.boundary_Iic,
          boundary_susp_succ (hm.boundary m α).nonempty]

def RDCpxUp.suspensionFunctor : RDCpxUp.{u} ⥤ RDCpxUp.{u} where
  obj P := ⟨suspension P.toOGP, isRDC_suspension P.isRDC⟩
  map f := ConcreteCategory.ofHom
    ⟨suspMap (ConcreteCategory.hom f), (ConcreteCategory.hom f).isComap.suspMap⟩
  map_id P := ConcreteCategory.hom_ext _ _ fun w => by
    cases w <;> rfl
  map_comp f g := ConcreteCategory.hom_ext _ _ fun w => by
    cases w <;> rfl

@[simp] theorem RDCpxUp.suspensionFunctor_map_apply {P Q : RDCpxUp.{u}} (f : P ⟶ Q)
    (w : suspension P.toOGP) :
    ConcreteCategory.hom (suspensionFunctor.map f) w = suspMap (ConcreteCategory.hom f) w :=
  rfl

instance : RDCpxUp.suspensionFunctor.{u}.Faithful where
  map_injective {_ _} f g h := ConcreteCategory.hom_ext f g fun x =>
    susp.inj (ConcreteCategory.congr_hom h (susp x))

end Suspension

section Dual

variable (J : ℕ → Bool) {P : OGP.{u}} {Q : OGP.{v}}

theorem IsComap.dual {c : P → Q} (hc : IsComap c) :
    IsComap (P := dual P J) (Q := dual Q J) c where
  monotone := hc.monotone
  isMoleculeIn_Iic y := (isMoleculeIn_dual J).2 (hc.isMoleculeIn_Iic y)
  boundary_Iic y n α := by
    rw [boundary_dual, boundary_dual]
    exact hc.boundary_Iic y n _

theorem isComap_dual_iff {c : P → Q} :
    IsComap (P := dual P J) (Q := dual Q J) c ↔ IsComap c :=
  ⟨fun hc => ⟨hc.monotone, fun y => (isMoleculeIn_dual J).1 (hc.isMoleculeIn_Iic y),
    fun y n α => by
      have h := hc.boundary_Iic y n (xor (J (n + 1)) α)
      rw [boundary_dual, boundary_dual, Bool.xor_xor_cancel_left] at h
      exact h⟩, IsComap.dual J⟩

def RDCpxUp.dualFunctor : RDCpxUp.{u} ⥤ RDCpxUp.{u} where
  obj P := ⟨dual P.toOGP J, P.isRDC.dual J⟩
  map f := ConcreteCategory.ofHom ⟨ConcreteCategory.hom f, (ConcreteCategory.hom f).isComap.dual J⟩

@[simp] theorem RDCpxUp.dualFunctor_map_apply {P Q : RDCpxUp.{u}} (f : P ⟶ Q) (x : P.toOGP) :
    ConcreteCategory.hom ((dualFunctor J).map f) x = ConcreteCategory.hom f x :=
  rfl

end Dual

section GrayProduct

variable {P P' Q Q' : OGP.{u}}

theorem lowerPreimage_prod {c : P → P'} {d : Q → Q'} (hc : Monotone c) (hd : Monotone d)
    (U : LowerSet P') (V : LowerSet Q') :
    lowerPreimage (P := grayProduct P Q) (Q := grayProduct P' Q') (monotone_prodMap hc hd)
      (U ×ˢ V) = lowerPreimage hc U ×ˢ lowerPreimage hd V :=
  rfl

private theorem IsComap.apply_mem_facesIn_Iic {R S : OGP.{u}} {c : R → S} (hc : IsComap c)
    {y : S} {m : ℕ} {α : Bool} {a : R}
    (ha : a ∈ R.facesIn (lowerPreimage hc.monotone (.Iic y)) m α) :
    c a ∈ S.facesIn (.Iic y) m α := by
  have hb : c a ∈ S.boundary (.Iic y) m α := by
    rw [← mem_lowerPreimage hc.monotone, hc.boundary_Iic]
    exact mem_boundary_of_mem_facesIn ha le_rfl
  exact mem_facesIn_of_mem_boundary hb
    (le_antisymm (grade_le_of_mem_boundary hb) (ha.2.1 ▸ hc.grade_le a))

private theorem IsComap.apply_eq_and_grade_eq_of_maximal {R S : OGP.{u}} {c : R → S}
    (hc : IsComap c) {y : S} {a : R} (ha : Maximal (· ∈ lowerPreimage hc.monotone (.Iic y)) a) :
    c a = y ∧ grade ℕ a = grade ℕ y := by
  have hge : grade ℕ y ≤ grade ℕ a := by
    refine not_lt.1 fun hlt => lt_irrefl (grade ℕ a) ?_
    have hab (β : Bool) :
        a ∈ R.boundary (lowerPreimage hc.monotone (.Iic y)) (grade ℕ a) β :=
      mem_boundary_of_mem_facesIn (maximal_mem_iff_forall_mem_facesIn.1 ha β) le_rfl
    exact hc.grade_lt_of_mem_inf_boundary_lowerPreimage_Iic hlt ⟨hab false, hab true⟩
  have hca : c a = y := GradeOrder.eq_of_le_of_grade_le ha.prop (hge.trans (hc.grade_le a))
  exact ⟨hca, le_antisymm (hca ▸ hc.grade_le a) hge⟩

theorem IsComap.prodMap {c : P → P'} {d : Q → Q'} (hc : IsComap c) (hd : IsComap d) :
    IsComap (P := grayProduct P Q) (Q := grayProduct P' Q') fun p => (c p.1, d p.2) where
  monotone := monotone_prodMap hc.monotone hd.monotone
  isMoleculeIn_Iic := fun ⟨x, y⟩ => by
    rw [Iic_grayProduct, lowerPreimage_prod hc.monotone hd.monotone]
    exact isMoleculeIn_prod (hc.isMoleculeIn_Iic x) (hd.isMoleculeIn_Iic y)
  boundary_Iic := fun ⟨x, y⟩ n α => by
    have hgM := (hc.isMoleculeIn_Iic x).isGlobular
    have hgN := (hd.isMoleculeIn_Iic y).isGlobular
    rw [Iic_grayProduct, lowerPreimage_prod hc.monotone hd.monotone]
    refine SetLike.ext fun ⟨a, b⟩ => ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨k, hk, hx, hy⟩ := LowerSet.mem_iSup₂_iff.1 (boundary_prod_le _ _ n α h)
      refine (mem_boundary_prod_of_isGlobular hgM hgN).2 ⟨k, hk, ?_, ?_⟩
      · rw [← hc.boundary_Iic]
        exact hx
      · rw [← hd.boundary_Iic]
        exact hy
    · obtain ⟨⟨a₀, b₀⟩, hg, hle⟩ := mem_boundary.1 h
      refine (mem_lowerPreimage _).2 (LowerSet.lower _ (a := (c a₀, d b₀)) (b := (c a, d b))
        ⟨hc.monotone hle.1, hd.monotone hle.2⟩ ?_)
      rcases hg with hf | ⟨hm, hlt⟩
      · obtain ⟨hn, ha, hb⟩ := mem_facesIn_prod.1 hf
        have ha' := hc.apply_mem_facesIn_Iic ha
        have hb' := hd.apply_mem_facesIn_Iic hb
        have hga : grade ℕ (c a₀) = grade ℕ a₀ := ha'.2.1
        have hgb : grade ℕ (d b₀) = grade ℕ b₀ := hb'.2.1
        refine mem_boundary_of_mem_facesIn (mem_facesIn_prod.2 ⟨by rw [hga, hgb, hn], ?_, ?_⟩)
          le_rfl
        · rwa [hga]
        · rwa [hga, hgb]
      · obtain ⟨hma, hmb⟩ := maximal_mem_prod_iff.1 hm
        obtain ⟨hca, hga⟩ := hc.apply_eq_and_grade_eq_of_maximal hma
        obtain ⟨hdb, hgb⟩ := hd.apply_eq_and_grade_eq_of_maximal hmb
        rw [hca, hdb]
        refine mem_boundary_of_maximal (maximal_mem_prod_iff.2 ⟨?_, ?_⟩) ?_ le_rfl
        · exact ⟨le_rfl, fun _ h _ => h⟩
        · exact ⟨le_rfl, fun _ h _ => h⟩
        · change grade ℕ x + grade ℕ y < n
          rw [← hga, ← hgb]
          exact hlt

def RDCpxUp.grayProductFunctor : RDCpxUp.{u} × RDCpxUp.{u} ⥤ RDCpxUp.{u} where
  obj X := ⟨grayProduct X.1.toOGP X.2.toOGP, isRDC_grayProduct X.1.isRDC X.2.isRDC⟩
  map f := ConcreteCategory.ofHom
    ⟨fun p => (ConcreteCategory.hom f.1 p.1, ConcreteCategory.hom f.2 p.2),
      (ConcreteCategory.hom f.1).isComap.prodMap (ConcreteCategory.hom f.2).isComap⟩

@[simp] theorem RDCpxUp.grayProductFunctor_map_apply {X Y : RDCpxUp.{u} × RDCpxUp.{u}}
    (f : X ⟶ Y) (p : grayProduct X.1.toOGP X.2.toOGP) :
    ConcreteCategory.hom (grayProductFunctor.map f) p =
      (ConcreteCategory.hom f.1 p.1, ConcreteCategory.hom f.2 p.2) :=
  rfl

end GrayProduct

section Join

variable {P P' Q Q' : OGP.{u}}

theorem lowerPreimage_joinPre {c : P → P'} {d : Q → Q'} (hc : Monotone c) (hd : Monotone d)
    (hΦ : Monotone (suspProdMap c d)) (W : LowerSet (grayProduct (suspension P') (suspension Q'))) :
    lowerPreimage (monotone_joinMap hc hd) (joinPre P' Q' W) = joinPre P Q (lowerPreimage hΦ W) :=
  SetLike.ext fun z => by
    rw [mem_lowerPreimage, mem_joinPre, mem_joinPre, mem_lowerPreimage, joinToGray_joinMap]

private theorem lowerPreimage_joinMap_Iic {c : P → P'} {d : Q → Q'} (hc : Monotone c)
    (hd : Monotone d) (z' : join P' Q') {U : LowerSet P} {V : LowerSet Q}
    (hU : ∀ x, x ∈ U ↔ (c x : WithBot P') ≤ z'.1.1)
    (hV : ∀ y, y ∈ V ↔ (d y : WithBot Q') ≤ z'.1.2) :
    lowerPreimage (monotone_joinMap hc hd) (.Iic z') = map (join.map (incl U) (incl V)) ⊤ := by
  have key {R R' : OGP.{u}} (f : R → R') (W : LowerSet R) (a' : WithBot R')
      (hW : ∀ x, x ∈ W ↔ (f x : WithBot R') ≤ a') (a : WithBot R) :
      WithBot.map f a ≤ a' ↔ botSusp R a ∈ W.susp := by
    induction a using WithBot.recBotCoe with
    | bot => exact iff_of_true bot_le (pole_mem_susp W true)
    | coe x => rw [WithBot.map_coe, botSusp_coe, susp_mem_susp, hW]
  rw [map_join_map_incl_top]
  exact SetLike.ext fun z => and_congr (key c U _ hU z.1.1) (key d V _ hV z.1.2)

theorem IsComap.joinMap {c : P → P'} {d : Q → Q'} (hc : IsComap c) (hd : IsComap d) :
    IsComap (joinMap c d) where
  monotone := monotone_joinMap hc.monotone hd.monotone
  isMoleculeIn_Iic z' := by
    have hPe : IsEmpty (P.restrict ⊥) := ⟨fun x => x.2⟩
    have hQe : IsEmpty (Q.restrict ⊥) := ⟨fun y => y.2⟩
    have hb {R R' : OGP.{u}} (f : R → R') (x : R) : x ∈ (⊥ : LowerSet R) ↔ (f x : WithBot R') ≤ ⊥ :=
      iff_of_false (fun h => h) fun h => WithBot.coe_ne_bot (le_bot_iff.1 h)
    have key (U : LowerSet P) (V : LowerSet Q) (hU : ∀ x, x ∈ U ↔ (c x : WithBot P') ≤ z'.1.1)
        (hV : ∀ y, y ∈ V ↔ (d y : WithBot Q') ≤ z'.1.2)
        (h : IsMolecule (join (P.restrict U) (Q.restrict V))) :
        (join P Q).IsMoleculeIn
          (lowerPreimage (monotone_joinMap hc.monotone hd.monotone) (.Iic z')) := by
      rw [lowerPreimage_joinMap_Iic hc.monotone hd.monotone z' hU hV]
      exact isMoleculeIn_map _ h
    match h₁ : z'.1.1, h₂ : z'.1.2 with
    | none, none => exact absurd (Prod.ext h₁ h₂) z'.2
    | none, some y' =>
      exact key ⊥ (lowerPreimage hd.monotone (.Iic y')) (fun x => by rw [h₁]; exact hb c x)
        (fun y => by rw [h₂]; exact WithBot.coe_le_coe.symm)
        (isMolecule_join_of_isEmpty_left ((isMolecule_restrict_iff _).2 (hd.isMoleculeIn_Iic y')))
    | some x', none =>
      exact key (lowerPreimage hc.monotone (.Iic x')) ⊥
        (fun x => by rw [h₁]; exact WithBot.coe_le_coe.symm) (fun y => by rw [h₂]; exact hb d y)
        (isMolecule_join_of_isEmpty_right ((isMolecule_restrict_iff _).2 (hc.isMoleculeIn_Iic x')))
    | some x', some y' =>
      exact key (lowerPreimage hc.monotone (.Iic x')) (lowerPreimage hd.monotone (.Iic y'))
        (fun x => by rw [h₁]; exact WithBot.coe_le_coe.symm)
        (fun y => by rw [h₂]; exact WithBot.coe_le_coe.symm)
        (isMolecule_join _ _ ((isMolecule_restrict_iff _).2 (hc.isMoleculeIn_Iic x'))
          ((isMolecule_restrict_iff _).2 (hd.isMoleculeIn_Iic y')))
  boundary_Iic z' n α := by
    have hΦ : IsComap (suspProdMap c d) := hc.suspMap.prodMap hd.suspMap
    rw [← joinPre_Iic z', ← joinPre_boundary_succ,
      lowerPreimage_joinPre hc.monotone hd.monotone hΦ.monotone,
      lowerPreimage_joinPre hc.monotone hd.monotone hΦ.monotone, hΦ.boundary_Iic,
      joinPre_boundary_succ]

theorem isRDC_join {P Q : OGP.{u}} (hP : IsRDC P) (hQ : IsRDC Q) : IsRDC (join P Q) := fun z => by
  have h := ((IsComap.id hP).joinMap (IsComap.id hQ)).isMoleculeIn_Iic z
  have he : lowerPreimage ((IsComap.id hP).joinMap (IsComap.id hQ)).monotone (.Iic z) = .Iic z :=
    SetLike.ext fun w => by
      have hw : joinMap (_root_.id : P → P) (_root_.id : Q → Q) w = w := congrFun joinMap_id w
      rw [mem_lowerPreimage, hw]
  rwa [he] at h

def RDCpxUp.joinFunctor : RDCpxUp.{u} × RDCpxUp.{u} ⥤ RDCpxUp.{u} where
  obj X := ⟨join X.1.toOGP X.2.toOGP, isRDC_join X.1.isRDC X.2.isRDC⟩
  map f := ConcreteCategory.ofHom
    ⟨joinMap (ConcreteCategory.hom f.1) (ConcreteCategory.hom f.2),
      (ConcreteCategory.hom f.1).isComap.joinMap (ConcreteCategory.hom f.2).isComap⟩
  map_id _ := ConcreteCategory.hom_ext _ _ fun z => congrFun joinMap_id z
  map_comp f g := ConcreteCategory.hom_ext _ _ fun z =>
    congrFun (joinMap_comp (ConcreteCategory.hom f.1) (ConcreteCategory.hom g.1)
      (ConcreteCategory.hom f.2) (ConcreteCategory.hom g.2)) z

@[simp] theorem RDCpxUp.joinFunctor_map_apply {X Y : RDCpxUp.{u} × RDCpxUp.{u}} (f : X ⟶ Y)
    (z : join X.1.toOGP X.2.toOGP) :
    ConcreteCategory.hom (joinFunctor.map f) z =
      joinMap (ConcreteCategory.hom f.1) (ConcreteCategory.hom f.2) z :=
  rfl

end Join

end Atoms.Molecule.OGP
