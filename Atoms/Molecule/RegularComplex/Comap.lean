import Atoms.Molecule.Interior
import Atoms.Molecule.RegularComplex.Basic
import Mathlib.Order.Category.PartOrd

universe u v w

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {Q : OGP.{v}} {R : OGP.{w}}

def lowerPreimage {c : P → Q} (hc : Monotone c) (V : LowerSet Q) : LowerSet P :=
  ⟨c ⁻¹' V, V.lower.preimage hc⟩

section LowerPreimage

variable {c : P → Q} (hc : Monotone c)

@[simp, norm_cast] theorem coe_lowerPreimage (V : LowerSet Q) :
    (lowerPreimage hc V : Set P) = c ⁻¹' V :=
  rfl

@[simp] theorem mem_lowerPreimage {V : LowerSet Q} {x : P} : x ∈ lowerPreimage hc V ↔ c x ∈ V :=
  Iff.rfl

@[simp] theorem lowerPreimage_top : lowerPreimage hc ⊤ = ⊤ :=
  rfl

@[simp] theorem lowerPreimage_bot : lowerPreimage hc ⊥ = ⊥ :=
  rfl

theorem lowerPreimage_sup (V W : LowerSet Q) :
    lowerPreimage hc (V ⊔ W) = lowerPreimage hc V ⊔ lowerPreimage hc W :=
  rfl

theorem lowerPreimage_inf (V W : LowerSet Q) :
    lowerPreimage hc (V ⊓ W) = lowerPreimage hc V ⊓ lowerPreimage hc W :=
  rfl

theorem lowerPreimage_comp {d : Q → R} (hd : Monotone d) (V : LowerSet R) :
    lowerPreimage (hd.comp hc) V = lowerPreimage hc (lowerPreimage hd V) :=
  rfl

end LowerPreimage

structure IsComap (c : P → Q) : Prop where
  monotone : Monotone c
  isMoleculeIn_Iic (y : Q) : IsMoleculeIn P (lowerPreimage monotone (.Iic y))
  boundary_Iic (y : Q) (n : ℕ) (α : Bool) :
    lowerPreimage monotone (Q.boundary (.Iic y) n α) =
      P.boundary (lowerPreimage monotone (.Iic y)) n α

namespace IsComap

variable {c : P → Q} (hc : IsComap c)
include hc

theorem grade_le (x : P) : grade ℕ x ≤ grade ℕ (c x) := by
  have h (α : Bool) : P.boundary (lowerPreimage hc.monotone (.Iic (c x))) (grade ℕ (c x)) α =
      lowerPreimage hc.monotone (.Iic (c x)) := by
    rw [← hc.boundary_Iic, boundary_eq_self (by rw [LowerSet.krullDim_Iic])]
  exact krullDim_le_coe_iff.1 (boundary_eq_self_iff.1 (h true))
    ⟨x, (mem_lowerPreimage hc.monotone).2 (LowerSet.mem_Iic_iff.2 le_rfl)⟩

theorem krullDim_lowerPreimage_le {V : LowerSet Q} {n : ℕ} (hV : krullDim V = n) :
    krullDim (lowerPreimage hc.monotone V) ≤ n :=
  krullDim_le_coe_iff.2 fun ⟨x, hx⟩ =>
    (hc.grade_le x).trans (krullDim_le_coe_iff.1 hV.le ⟨c x, hx⟩)

private theorem isPastingIn_lowerPreimage_of_boundary {k : ℕ} {V W U : LowerSet Q}
    (hp : Q.IsPastingIn k V W U)
    (hV : lowerPreimage hc.monotone (Q.boundary V k true) =
      P.boundary (lowerPreimage hc.monotone V) k true)
    (hW : lowerPreimage hc.monotone (Q.boundary W k false) =
      P.boundary (lowerPreimage hc.monotone W) k false) :
    P.IsPastingIn k (lowerPreimage hc.monotone V) (lowerPreimage hc.monotone W)
      (lowerPreimage hc.monotone U) where
  sup_eq := by rw [← lowerPreimage_sup, hp.sup_eq]
  inf_eq_output := by rw [← lowerPreimage_inf, hp.inf_eq_output, hV]
  inf_eq_input := by rw [← lowerPreimage_inf, hp.inf_eq_input, hW]

omit hc in
private theorem grade_lt_of_mem_inf_boundary_Iic {y z : Q} {m : ℕ} (hm : m < grade ℕ y)
    (hz : z ∈ Q.boundary (.Iic y) m false ⊓ Q.boundary (.Iic y) m true) : grade ℕ z < m := by
  have hzb (β : Bool) : z ∈ Q.boundary (.Iic y) m β := by
    cases β
    exacts [hz.1, hz.2]
  refine (grade_le_of_mem_boundary hz.1).lt_of_ne fun hzm => ?_
  have hf (β : Bool) : z ∈ Q.facesIn (LowerSet.Iic y) m β := mem_facesIn_of_mem_boundary (hzb β) hzm
  have hzy : z < y := lt_of_le_of_ne (hf false).1 fun h => by rw [h] at hzm; omega
  obtain ⟨w, hzw, hwy⟩ := exists_covBy_le_of_lt hzy
  refine disjoint_left.1 (hf (!Q.orient hzw)).2.2 ?_ (LowerSet.mem_Iic_iff.2 hwy)
  rw [Bool.not_not]
  exact ⟨hzw, rfl⟩

theorem grade_lt_of_mem_inf_boundary_lowerPreimage_Iic {y : Q} {m : ℕ} (hm : m < grade ℕ y)
    {x : P} (hx : x ∈ P.boundary (lowerPreimage hc.monotone (.Iic y)) m false ⊓
      P.boundary (lowerPreimage hc.monotone (.Iic y)) m true) : grade ℕ x < m := by
  have hxm : x ∈ lowerPreimage hc.monotone (Q.boundary (.Iic y) m false ⊓
      Q.boundary (.Iic y) m true) := by
    rw [lowerPreimage_inf, hc.boundary_Iic, hc.boundary_Iic]
    exact hx
  exact (hc.grade_le x).trans_lt (grade_lt_of_mem_inf_boundary_Iic hm hxm)

private theorem exists_mem_lowerPreimage_Iic_grade_le (y : Q) :
    ∃ x ∈ lowerPreimage hc.monotone (.Iic y), grade ℕ y ≤ grade ℕ x := by
  set U := lowerPreimage hc.monotone (.Iic y)
  have key (m : ℕ) (hm : m < grade ℕ y) (hall : ∀ x ∈ U, grade ℕ x ≤ m) (x : P) (hx : x ∈ U) :
      grade ℕ x < m := by
    have hU (β : Bool) : P.boundary U m β = U :=
      boundary_eq_self (krullDim_le_coe_iff.2 fun z => hall z z.2) β
    refine hc.grade_lt_of_mem_inf_boundary_lowerPreimage_Iic hm ?_
    rw [hU, hU, inf_idem]
    exact hx
  have hlow (m : ℕ) : m < grade ℕ y → ¬ ∀ x ∈ U, grade ℕ x ≤ m := by
    induction m with
    | zero =>
      intro hm hall
      obtain ⟨x, hx⟩ : (U : Set P).Nonempty := (hc.isMoleculeIn_Iic y).nonempty
      exact Nat.not_lt_zero _ (key 0 hm hall x hx)
    | succ j ih =>
      exact fun hm hall => ih (by omega) fun x hx => Nat.lt_succ_iff.1 (key _ hm hall x hx)
  by_contra hne
  simp only [not_exists, not_and, not_le] at hne
  obtain ⟨x, hx⟩ : (U : Set P).Nonempty := (hc.isMoleculeIn_Iic y).nonempty
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (n := grade ℕ y) (by
    have := hne x hx
    omega)
  exact hlow n (by omega) fun z hz => by
    have := hne z hz
    omega

theorem surjective : Function.Surjective c := fun y => by
  obtain ⟨x, hx, hle⟩ := hc.exists_mem_lowerPreimage_Iic_grade_le y
  exact ⟨x, GradeOrder.eq_of_le_of_grade_le hx (hle.trans (hc.grade_le x))⟩

theorem krullDim_lowerPreimage_Iic (y : Q) :
    krullDim (lowerPreimage hc.monotone (.Iic y)) = krullDim (LowerSet.Iic y) := by
  obtain ⟨x, hx, hle⟩ := hc.exists_mem_lowerPreimage_Iic_grade_le y
  rw [LowerSet.krullDim_Iic]
  refine le_antisymm (hc.krullDim_lowerPreimage_le (LowerSet.krullDim_Iic y)) ?_
  exact (by exact_mod_cast hle : (grade ℕ y : WithBot ℕ∞) ≤ grade ℕ x).trans
    (grade_le_krullDim (⟨x, hx⟩ : ↥(lowerPreimage hc.monotone (.Iic y))))

private theorem isMoleculeIn_and_boundary {V : LowerSet Q} (hV : IsMoleculeIn Q V) :
    IsMoleculeIn P (lowerPreimage hc.monotone V) ∧
      krullDim (lowerPreimage hc.monotone V) = krullDim V ∧
      ∀ (n : ℕ) (α : Bool), lowerPreimage hc.monotone (Q.boundary V n α) =
        P.boundary (lowerPreimage hc.monotone V) n α := by
  induction hV with
  | point x _ => exact ⟨hc.isMoleculeIn_Iic x, hc.krullDim_lowerPreimage_Iic x, hc.boundary_Iic x⟩
  | atom t _ _ _ =>
    exact ⟨hc.isMoleculeIn_Iic t, hc.krullDim_lowerPreimage_Iic t, hc.boundary_Iic t⟩
  | paste k V W U hp hVm hWm hk ihV ihW =>
    obtain ⟨hV1, hV2, hV3⟩ := ihV
    obtain ⟨hW1, hW2, hW3⟩ := ihW
    have hpL := hc.isPastingIn_lowerPreimage_of_boundary hp (hV3 k true) (hW3 k false)
    refine ⟨.paste k _ _ _ hpL hV1 hW1 (by rwa [hV2, hW2]), ?_, fun n δ => ?_⟩
    · rw [← hp.sup_eq, lowerPreimage_sup, LowerSet.krullDim_sup, LowerSet.krullDim_sup, hV2, hW2]
    · have hgV := hVm.isGlobular
      have hgW := hWm.isGlobular
      have hgV' := hV1.isGlobular
      have hgW' := hW1.isGlobular
      rcases le_or_gt n k with hn | hn
      · cases δ
        · rw [hp.boundary_eq_of_le_cond false hgW hgV hn,
            hpL.boundary_eq_of_le_cond false hgW' hgV' hn, hV3]
        · rw [hp.boundary_eq_of_le_cond true hgV hgW hn,
            hpL.boundary_eq_of_le_cond true hgV' hgW' hn, hW3]
      · rw [hp.boundary_eq_sup_of_lt_cond false hgW hgV hn,
          hpL.boundary_eq_sup_of_lt_cond false hgW' hgV' hn, lowerPreimage_sup, hW3, hV3]

theorem isMoleculeIn {V : LowerSet Q} (hV : IsMoleculeIn Q V) :
    IsMoleculeIn P (lowerPreimage hc.monotone V) :=
  (hc.isMoleculeIn_and_boundary hV).1

theorem krullDim_lowerPreimage {V : LowerSet Q} (hV : IsMoleculeIn Q V) :
    krullDim (lowerPreimage hc.monotone V) = krullDim V :=
  (hc.isMoleculeIn_and_boundary hV).2.1

theorem lowerPreimage_boundary {V : LowerSet Q} (hV : IsMoleculeIn Q V) (n : ℕ) (α : Bool) :
    lowerPreimage hc.monotone (Q.boundary V n α) =
      P.boundary (lowerPreimage hc.monotone V) n α :=
  (hc.isMoleculeIn_and_boundary hV).2.2 n α

theorem isPastingIn_lowerPreimage {k : ℕ} {V W U : LowerSet Q} (hV : IsMoleculeIn Q V)
    (hW : IsMoleculeIn Q W) (hp : Q.IsPastingIn k V W U) :
    P.IsPastingIn k (lowerPreimage hc.monotone V) (lowerPreimage hc.monotone W)
      (lowerPreimage hc.monotone U) :=
  hc.isPastingIn_lowerPreimage_of_boundary hp (hc.lowerPreimage_boundary hV k true)
    (hc.lowerPreimage_boundary hW k false)

theorem isMolecule (hQ : IsMolecule Q) : IsMolecule P :=
  hc.isMoleculeIn hQ

theorem lowerPreimage_bdry {V : LowerSet Q} (hV : IsMoleculeIn Q V) (α : Bool) :
    lowerPreimage hc.monotone (Q.bdry V α) = P.bdry (lowerPreimage hc.monotone V) α := by
  obtain ⟨d, hd⟩ := hV.exists_krullDim_eq
  have hd' : krullDim (lowerPreimage hc.monotone V) = d := (hc.krullDim_lowerPreimage hV).trans hd
  rcases d with _ | m
  · rw [bdry_eq_bot hd.le, bdry_eq_bot hd'.le, lowerPreimage_bot]
  · rw [bdry_eq_boundary (by rw [hd]; push_cast; rfl),
      bdry_eq_boundary (by rw [hd']; push_cast; rfl), hc.lowerPreimage_boundary hV]

theorem lowerPreimage_properBoundary {V : LowerSet Q} (hV : IsMoleculeIn Q V) :
    lowerPreimage hc.monotone (Q.properBoundary V) =
      P.properBoundary (lowerPreimage hc.monotone V) := by
  rw [hV.properBoundary_eq_bdryFull, (hc.isMoleculeIn hV).properBoundary_eq_bdryFull, bdryFull,
    bdryFull, lowerPreimage_sup, hc.lowerPreimage_bdry hV, hc.lowerPreimage_bdry hV]

theorem preimage_interior {V : LowerSet Q} (hV : IsMoleculeIn Q V) :
    c ⁻¹' Q.interior V = P.interior (lowerPreimage hc.monotone V) := by
  rw [OGP.interior, OGP.interior, preimage_sdiff, ← hc.lowerPreimage_properBoundary hV]
  rfl

theorem preimage_interior_boundary {V : LowerSet Q} (hV : IsMoleculeIn Q V) (n : ℕ) (α : Bool) :
    c ⁻¹' Q.interior (Q.boundary V n α) =
      P.interior (P.boundary (lowerPreimage hc.monotone V) n α) := by
  rw [hc.preimage_interior (hV.boundary n α), hc.lowerPreimage_boundary hV]

theorem isRound_lowerPreimage {V : LowerSet Q} (hV : IsMoleculeIn Q V) (hr : Q.IsRound V) :
    P.IsRound (lowerPreimage hc.monotone V) where
  isGlobular := (hc.isMoleculeIn hV).isGlobular
  inf_boundary_zero h := by
    rw [← hc.lowerPreimage_boundary hV, ← hc.lowerPreimage_boundary hV, ← lowerPreimage_inf,
      hr.inf_boundary_zero (hc.krullDim_lowerPreimage hV ▸ h), lowerPreimage_bot]
  inf_boundary_succ n h := by
    rw [← hc.lowerPreimage_boundary hV, ← hc.lowerPreimage_boundary hV, ← lowerPreimage_inf,
      hr.inf_boundary_succ n (hc.krullDim_lowerPreimage hV ▸ h), boundaryFull, boundaryFull,
      lowerPreimage_sup, hc.lowerPreimage_boundary hV, hc.lowerPreimage_boundary hV]

theorem facesIn_eq (hQ : IsMolecule Q) (n : ℕ) (α : Bool) :
    P.facesIn ⊤ n α = {x | x ∈ c ⁻¹' Q.facesIn ⊤ n α ∧ grade ℕ x = n} := by
  have hb := hc.lowerPreimage_boundary hQ n α
  rw [lowerPreimage_top] at hb
  ext x
  refine ⟨fun hx => ⟨?_, hx.2.1⟩, fun ⟨hx, hxn⟩ => ?_⟩
  · have hxb : c x ∈ Q.boundary ⊤ n α := by
      rw [← mem_lowerPreimage hc.monotone, hb]
      exact mem_boundary_of_mem_facesIn hx le_rfl
    exact mem_facesIn_of_mem_boundary hxb (le_antisymm (grade_le_of_mem_boundary hxb)
      (hx.2.1 ▸ hc.grade_le x))
  · have hxb : x ∈ P.boundary ⊤ n α := by
      rw [← hb, mem_lowerPreimage]
      exact mem_boundary_of_mem_facesIn hx le_rfl
    exact mem_facesIn_of_mem_boundary hxb hxn

omit hc in
theorem id {P : OGP.{u}} (hP : IsRDC P) : IsComap (_root_.id : P → P) where
  monotone := monotone_id
  isMoleculeIn_Iic := hP
  boundary_Iic _ _ _ := rfl

theorem comp {d : Q → R} (hd : IsComap d) : IsComap (d ∘ c) where
  monotone := hd.monotone.comp hc.monotone
  isMoleculeIn_Iic z := hc.isMoleculeIn (hd.isMoleculeIn_Iic z)
  boundary_Iic z n α := by
    rw [lowerPreimage_comp hc.monotone hd.monotone, lowerPreimage_comp hc.monotone hd.monotone,
      hd.boundary_Iic, hc.lowerPreimage_boundary (hd.isMoleculeIn_Iic z)]

end IsComap

theorem lowerPreimage_hom {P Q : OGP.{u}} (e : P ≅ Q) (V : LowerSet Q) :
    lowerPreimage (isMorphism e.hom).monotone V = map e.inv V :=
  SetLike.ext fun x => by
    rw [mem_lowerPreimage, mem_map]
    refine ⟨fun hx => ⟨e.hom x, hx, Iso.hom_inv_id_apply e x⟩, fun ⟨y, hy, hyx⟩ => ?_⟩
    rw [← hyx, Iso.inv_hom_id_apply]
    exact hy

theorem isComap_iso {P Q : OGP.{u}} (e : P ≅ Q) (hQ : IsRDC Q) : IsComap ⇑e.hom where
  monotone := (isMorphism e.hom).monotone
  isMoleculeIn_Iic y := by
    rw [lowerPreimage_hom]
    exact isMoleculeIn_map e.inv (hQ y)
  boundary_Iic y n α := by rw [lowerPreimage_hom, lowerPreimage_hom, map_boundary]

private theorem mem_faces_iff_covBy_and_mem_boundary {α : Bool} {x y : P} :
    y ∈ P.faces α x ↔ y ⋖ x ∧ y ∈ P.boundary (.Iic x) (grade ℕ y) α := by
  refine ⟨fun h => ⟨h.1, ?_⟩, fun ⟨hyx, hy⟩ => ?_⟩
  · rw [boundary_Iic (Nat.covBy_iff_add_one_eq.1 (h.1.grade ℕ)).symm]
    exact subset_lowerClosure h
  · have hd := Nat.covBy_iff_add_one_eq.1 (hyx.grade ℕ)
    rw [← bdry_eq_boundary (by rw [LowerSet.krullDim_Iic, ← hd]; push_cast; rfl)] at hy
    exact mem_faces_of_mem_bdry_Iic hy hd

theorem IsComap.isMorphism_of_lowerPreimage_Iic {c : P → Q} (hc : IsComap c)
    (hb : Function.Bijective c) (hIic : ∀ x, lowerPreimage hc.monotone (.Iic (c x)) = .Iic x) :
    IsMorphism c := by
  have hle {a b : P} : c a ≤ c b ↔ a ≤ b := by
    rw [← LowerSet.mem_Iic_iff, ← LowerSet.mem_Iic_iff, ← hIic, mem_lowerPreimage]
  let e : P ≃o Q := ⟨Equiv.ofBijective c hb, hle⟩
  have hgrade (y : P) : grade ℕ (c y) = grade ℕ y := by
    have h := hc.krullDim_lowerPreimage_Iic (c y)
    rw [hIic, LowerSet.krullDim_Iic, LowerSet.krullDim_Iic] at h
    exact_mod_cast h.symm
  have hfaces (α : Bool) (x y : P) : c y ∈ Q.faces α (c x) ↔ y ∈ P.faces α x := by
    rw [mem_faces_iff_covBy_and_mem_boundary, mem_faces_iff_covBy_and_mem_boundary, hgrade,
      ← hIic x, ← hc.boundary_Iic, mem_lowerPreimage]
    exact and_congr_left' (apply_covBy_apply_iff e)
  refine ⟨fun x α => ⟨fun y hy => (hfaces α x y).2 hy, hb.1.injOn, fun z hz => ?_⟩⟩
  obtain ⟨y, rfl⟩ := hb.2 z
  exact ⟨y, (hfaces α x y).1 hz, rfl⟩

theorem IsComap.isMorphism_of_inverse {c : P → Q} {d : Q → P} (hc : IsComap c) (hd : IsComap d)
    (hdc : Function.LeftInverse d c) (hcd : Function.RightInverse d c) : IsMorphism c :=
  hc.isMorphism_of_lowerPreimage_Iic ⟨hdc.injective, hcd.surjective⟩ fun x =>
    SetLike.ext fun z => by
      rw [mem_lowerPreimage, LowerSet.mem_Iic_iff, LowerSet.mem_Iic_iff]
      exact ⟨fun h => (hdc z).ge.trans ((hd.monotone h).trans (hdc x).le), fun h => hc.monotone h⟩

structure Comap (P : OGP.{u}) (Q : OGP.{v}) where
  toFun : P → Q
  isComap : IsComap toFun

namespace Comap

instance : FunLike (Comap P Q) P Q where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

@[ext] theorem ext {f g : Comap P Q} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

def id (P : OGP.{u}) (hP : IsRDC P) : Comap P P := ⟨_root_.id, IsComap.id hP⟩

def comp (g : Comap Q R) (f : Comap P Q) : Comap P R := ⟨g ∘ f, f.isComap.comp g.isComap⟩

@[simp] theorem id_apply (hP : IsRDC P) (x : P) : Comap.id P hP x = x := rfl

@[simp] theorem comp_apply (g : Comap Q R) (f : Comap P Q) (x : P) : g.comp f x = g (f x) := rfl

end Comap

@[implicit_reducible] def RDCpxUp : Type (u + 1) := RDCpxDown.{u}

namespace RDCpxUp

instance : CoeSort RDCpxUp.{u} (Type u) := ⟨fun P => P.toOGP⟩

@[ext] structure Hom (P Q : RDCpxUp.{u}) where
  private mk ::
  hom' : Comap P.toOGP Q.toOGP

instance : Category RDCpxUp.{u} where
  Hom := Hom
  id P := ⟨Comap.id P.toOGP P.isRDC⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory RDCpxUp.{u} fun P Q => Comap P.toOGP Q.toOGP where
  hom := Hom.hom'
  ofHom := Hom.mk

def forget : RDCpxUp.{u} ⥤ PartOrd.{u} where
  obj P := PartOrd.of P.toOGP
  map f := PartOrd.ofHom ⟨ConcreteCategory.hom f, (ConcreteCategory.hom f).isComap.monotone⟩

instance : forget.{u}.Faithful where
  map_injective {_ _} f g h := ConcreteCategory.hom_ext f g fun x => ConcreteCategory.congr_hom h x

end RDCpxUp

end Atoms.Molecule.OGP
