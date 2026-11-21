import Atoms.ForMathlib.Data.Bool
import Atoms.Molecule.Transport
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Types.Pushouts

universe u

open CategoryTheory Limits Order Set

namespace Atoms.Molecule.OGP

variable {P Q : OGP.{u}} {S : LowerSet P} {T : LowerSet Q} (φ : P.restrict S ≅ Q.restrict T)

def GlueCarrier : Type u :=
  Types.Pushout (↾(Subtype.val : ↥S → P)) (↾fun s : ↥S => ((φ.hom s : Q.restrict T) : Q))

instance : Mono (↾(Subtype.val : ↥S → P)) := (mono_iff_injective _).2 Subtype.val_injective

instance : Mono (↾fun s : ↥S => ((φ.hom s : Q.restrict T) : Q)) :=
  (mono_iff_injective _).2 fun _ _ h => IsInclusion.injective (f := φ.hom) (Subtype.ext h)

namespace GlueCarrier

def inl (p : P) : GlueCarrier φ := Quot.mk _ (Sum.inl p)

def inr (q : Q) : GlueCarrier φ := Quot.mk _ (Sum.inr q)

variable {φ}

theorem exists_inl_or_inr (x : GlueCarrier φ) : (∃ p, inl φ p = x) ∨ ∃ q, inr φ q = x := by
  rcases x with ⟨p | q⟩
  exacts [.inl ⟨p, rfl⟩, .inr ⟨q, rfl⟩]

theorem inl_eq_inr_of_mem {p : P} (h : p ∈ S) :
    inl φ p = inr φ ((φ.hom ⟨p, h⟩ : Q.restrict T) : Q) :=
  Quot.sound (Types.Pushout.Rel.inl_inr (⟨p, h⟩ : ↥S))

theorem inl_eq_inr_iff {p : P} {q : Q} :
    inl φ p = inr φ q ↔ ∃ h : p ∈ S, ((φ.hom ⟨p, h⟩ : Q.restrict T) : Q) = q := by
  refine (Types.Pushout.inl_eq_inr_iff _ _ p q).trans ⟨?_, ?_⟩
  · rintro ⟨s, rfl, rfl⟩
    exact ⟨s.2, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨⟨p, h⟩, rfl, rfl⟩

theorem inr_eq_inl_of_mem {q : Q} (h : q ∈ T) :
    inr φ q = inl φ ((φ.inv ⟨q, h⟩ : P.restrict S) : P) :=
  (inl_eq_inr_iff.2 ⟨(φ.inv ⟨q, h⟩).2, congrArg Subtype.val (φ.inv_hom_id_apply ⟨q, h⟩)⟩).symm

theorem inl_injective : Function.Injective (inl φ) :=
  (mono_iff_injective (Types.Pushout.inl _ _)).1 inferInstance

theorem inr_injective : Function.Injective (inr φ) :=
  (mono_iff_injective (Types.Pushout.inr _ _)).1 inferInstance

instance : LE (GlueCarrier φ) where
  le x y := (∃ p p', inl φ p = x ∧ inl φ p' = y ∧ p ≤ p') ∨
    ∃ q q', inr φ q = x ∧ inr φ q' = y ∧ q ≤ q'

theorem le_def {x y : GlueCarrier φ} :
    x ≤ y ↔ (∃ p p', inl φ p = x ∧ inl φ p' = y ∧ p ≤ p') ∨
      ∃ q q', inr φ q = x ∧ inr φ q' = y ∧ q ≤ q' :=
  Iff.rfl

theorem inl_le_inl {p p' : P} (h : p ≤ p') : inl φ p ≤ inl φ p' := .inl ⟨p, p', rfl, rfl, h⟩

theorem inr_le_inr {q q' : Q} (h : q ≤ q') : inr φ q ≤ inr φ q' := .inr ⟨q, q', rfl, rfl, h⟩

theorem inl_le_inl_iff {p p' : P} : inl φ p ≤ inl φ p' ↔ p ≤ p' := by
  refine ⟨fun h => ?_, inl_le_inl⟩
  rcases h with ⟨_, _, h₁, h₁', h⟩ | ⟨q, q', hq, hq', h⟩
  · obtain rfl := inl_injective h₁
    obtain rfl := inl_injective h₁'
    exact h
  · obtain ⟨hp, rfl⟩ := inl_eq_inr_iff.1 hq.symm
    obtain ⟨hp', rfl⟩ := inl_eq_inr_iff.1 hq'.symm
    exact Subtype.coe_le_coe.2 ((IsInclusion.le_iff (f := φ.hom)).1 (Subtype.coe_le_coe.1 h))

theorem inl_le_inr_iff {p : P} {q : Q} :
    inl φ p ≤ inr φ q ↔ ∃ h : p ∈ S, ((φ.hom ⟨p, h⟩ : Q.restrict T) : Q) ≤ q := by
  constructor
  · rintro (⟨_, p', h₁, h₁', h⟩ | ⟨q₁, _, hq, hq', h⟩)
    · obtain rfl := inl_injective h₁
      obtain ⟨hp', rfl⟩ := inl_eq_inr_iff.1 h₁'
      exact ⟨S.lower h hp', Subtype.coe_le_coe.2 ((isMorphism φ.hom).monotone
        (Subtype.coe_le_coe.1 h))⟩
    · obtain ⟨hp, rfl⟩ := inl_eq_inr_iff.1 hq.symm
      obtain rfl := inr_injective hq'
      exact ⟨hp, h⟩
  · rintro ⟨h, hle⟩
    rw [inl_eq_inr_of_mem h]
    exact inr_le_inr hle

theorem exists_inl_eq_of_le_inl {x : GlueCarrier φ} {p : P} (h : x ≤ inl φ p) :
    ∃ p', inl φ p' = x := by
  rcases h with ⟨p', _, hp', -, -⟩ | ⟨q, _, hq, hq', hle⟩
  · exact ⟨p', hp'⟩
  · obtain ⟨hp, rfl⟩ := inl_eq_inr_iff.1 hq'.symm
    exact ⟨_, (inr_eq_inl_of_mem (T.lower hle (φ.hom ⟨p, hp⟩).2)).symm.trans hq⟩

variable (φ) in
def swapEquiv : GlueCarrier φ ≃ GlueCarrier φ.symm where
  toFun := Quot.lift (fun a : P ⊕ Q => Quot.mk _ a.swap) (by
    rintro _ _ ⟨s⟩
    exact inr_eq_inl_of_mem (φ := φ.symm) s.2)
  invFun := Quot.lift (fun a : Q ⊕ P => Quot.mk _ a.swap) (by
    rintro _ _ ⟨t⟩
    exact inr_eq_inl_of_mem t.2)
  left_inv := by rintro ⟨p | q⟩ <;> rfl
  right_inv := by rintro ⟨q | p⟩ <;> rfl

@[simp] theorem swapEquiv_inl (p : P) : swapEquiv φ (inl φ p) = inr φ.symm p := rfl

@[simp] theorem swapEquiv_inr (q : Q) : swapEquiv φ (inr φ q) = inl φ.symm q := rfl

variable (φ) in
def swap : GlueCarrier φ ≃o GlueCarrier φ.symm where
  toEquiv := swapEquiv φ
  map_rel_iff' {x y} := by
    rw [le_def, le_def, or_comm]
    refine or_congr (exists₂_congr fun p p' => ?_) (exists₂_congr fun q q' => ?_)
    · rw [← swapEquiv_inl, ← swapEquiv_inl, Equiv.apply_eq_iff_eq, Equiv.apply_eq_iff_eq]
    · rw [← swapEquiv_inr, ← swapEquiv_inr, Equiv.apply_eq_iff_eq, Equiv.apply_eq_iff_eq]

@[simp] theorem swap_inl (p : P) : swap φ (inl φ p) = inr φ.symm p := rfl

@[simp] theorem swap_inr (q : Q) : swap φ (inr φ q) = inl φ.symm q := rfl

theorem inr_le_inr_iff {q q' : Q} : inr φ q ≤ inr φ q' ↔ q ≤ q' := by
  rw [← (swap φ).le_iff_le, swap_inr, swap_inr]
  exact inl_le_inl_iff

theorem inr_le_inl_iff {q : Q} {p : P} :
    inr φ q ≤ inl φ p ↔ ∃ h : q ∈ T, ((φ.inv ⟨q, h⟩ : P.restrict S) : P) ≤ p := by
  rw [← (swap φ).le_iff_le, swap_inr, swap_inl]
  exact inl_le_inr_iff

theorem exists_inr_eq_of_le_inr {x : GlueCarrier φ} {q : Q} (h : x ≤ inr φ q) :
    ∃ q', inr φ q' = x := by
  rw [← (swap φ).le_iff_le, swap_inr] at h
  obtain ⟨q', hq'⟩ := exists_inl_eq_of_le_inl h
  exact ⟨q', (swap φ).injective ((swap_inr q').trans hq')⟩

instance : PartialOrder (GlueCarrier φ) where
  le_refl x := (exists_inl_or_inr x).elim (fun ⟨_, h⟩ => h ▸ inl_le_inl le_rfl)
    fun ⟨_, h⟩ => h ▸ inr_le_inr le_rfl
  le_trans x y z hxy hyz := by
    rcases exists_inl_or_inr z with ⟨p, rfl⟩ | ⟨q, rfl⟩
    · obtain ⟨p', rfl⟩ := exists_inl_eq_of_le_inl hyz
      obtain ⟨p'', rfl⟩ := exists_inl_eq_of_le_inl hxy
      exact inl_le_inl ((inl_le_inl_iff.1 hxy).trans (inl_le_inl_iff.1 hyz))
    · obtain ⟨q', rfl⟩ := exists_inr_eq_of_le_inr hyz
      obtain ⟨q'', rfl⟩ := exists_inr_eq_of_le_inr hxy
      exact inr_le_inr ((inr_le_inr_iff.1 hxy).trans (inr_le_inr_iff.1 hyz))
  le_antisymm x y hxy hyx := by
    rcases exists_inl_or_inr y with ⟨p, rfl⟩ | ⟨q, rfl⟩
    · obtain ⟨p', rfl⟩ := exists_inl_eq_of_le_inl hxy
      exact congrArg (inl φ) (le_antisymm (inl_le_inl_iff.1 hxy) (inl_le_inl_iff.1 hyx))
    · obtain ⟨q', rfl⟩ := exists_inr_eq_of_le_inr hxy
      exact congrArg (inr φ) (le_antisymm (inr_le_inr_iff.1 hxy) (inr_le_inr_iff.1 hyx))

variable (φ) in
def inlSeg : P ≤i GlueCarrier φ where
  toRelEmbedding := (OrderEmbedding.ofMapLEIff (inl φ) fun _ _ => inl_le_inl_iff).ltEmbedding
  mem_range_of_rel' _ _ h := exists_inl_eq_of_le_inl h.le

@[simp] theorem inlSeg_apply (p : P) : inlSeg φ p = inl φ p := rfl

variable (φ) in
def inrSeg : Q ≤i GlueCarrier φ := (inlSeg φ.symm).trans (swap φ).symm.toInitialSeg

@[simp] theorem inrSeg_apply (q : Q) : inrSeg φ q = inr φ q := rfl

theorem inl_covBy_inl_iff {p p' : P} : inl φ p' ⋖ inl φ p ↔ p' ⋖ p :=
  (inlSeg φ).apply_covBy_apply_iff

theorem inr_covBy_inr_iff {q q' : Q} : inr φ q' ⋖ inr φ q ↔ q' ⋖ q :=
  (inrSeg φ).apply_covBy_apply_iff

variable (φ) in
protected def grade : GlueCarrier φ → ℕ :=
  Quot.lift (Sum.elim (grade ℕ) (grade ℕ)) (by
    rintro _ _ ⟨s⟩
    exact ((isMorphism (φ.hom ≫ incl T)).grade_eq s).symm)

instance : GradeMinOrder ℕ (GlueCarrier φ) :=
  .ofInitialSeg (GlueCarrier.grade φ) (inlSeg φ) (inrSeg φ) (fun _ => rfl) (fun _ => rfl)
    fun x => (exists_inl_or_inr x).imp (fun ⟨p, h⟩ => ⟨p, h⟩) fun ⟨q, h⟩ => ⟨q, h⟩

variable (φ) in
theorem covBy_hom_val {s s' : S} :
    ((φ.hom s' : Q.restrict T) : Q) ⋖ (φ.hom s : Q.restrict T) ↔ (s' : P) ⋖ s :=
  (LowerSet.coe_covBy_coe T).trans
    ((IsInclusion.covBy_iff φ.hom).trans (LowerSet.coe_covBy_coe S).symm)

variable (φ) in
theorem orient_hom_val {s s' : S} (h : (s' : P) ⋖ s) :
    Q.orient ((covBy_hom_val φ).2 h) = P.orient h :=
  (isMorphism φ.hom).orient_apply ((LowerSet.coe_covBy_coe S).1 h)

variable (φ) in
def IsOut (x y : GlueCarrier φ) : Prop :=
  (∃ (p p' : P) (h : p' ⋖ p), inl φ p = x ∧ inl φ p' = y ∧ P.orient h = true) ∨
    ∃ (q q' : Q) (h : q' ⋖ q), inr φ q = x ∧ inr φ q' = y ∧ Q.orient h = true

theorem isOut_inl_inl_iff {p p' : P} (h : p' ⋖ p) :
    IsOut φ (inl φ p) (inl φ p') ↔ P.orient h = true := by
  constructor
  · rintro (⟨_, _, _, e, e', ho⟩ | ⟨_, _, h₁, e, e', ho⟩)
    · obtain rfl := inl_injective e
      obtain rfl := inl_injective e'
      exact ho
    · obtain ⟨hp, rfl⟩ := inl_eq_inr_iff.1 e.symm
      obtain ⟨hp', rfl⟩ := inl_eq_inr_iff.1 e'.symm
      exact (orient_hom_val φ h).symm.trans ho
  · exact fun ho => .inl ⟨p, p', h, rfl, rfl, ho⟩

theorem isOut_swap {x y : GlueCarrier φ} : IsOut φ.symm (swap φ x) (swap φ y) ↔ IsOut φ x y := by
  rw [IsOut, IsOut, or_comm]
  refine or_congr (exists₂_congr fun p p' => exists_congr fun h => ?_)
    (exists₂_congr fun q q' => exists_congr fun h => ?_)
  · rw [← swap_inl, ← swap_inl, (swap φ).injective.eq_iff, (swap φ).injective.eq_iff]
  · rw [← swap_inr, ← swap_inr, (swap φ).injective.eq_iff, (swap φ).injective.eq_iff]

theorem isOut_inr_inr_iff {q q' : Q} (h : q' ⋖ q) :
    IsOut φ (inr φ q) (inr φ q') ↔ Q.orient h = true := by
  rw [← isOut_swap, swap_inr, swap_inr]
  exact isOut_inl_inl_iff h

variable (φ) in
protected def orientData (x y : GlueCarrier φ) :
    y ⋖ x → {b : Bool // b = true ↔ IsOut φ x y} :=
  Quot.recOnSubsingleton₂ x y fun (a b : P ⊕ Q) => match a, b with
    | .inl p, .inl p' => fun (h : inl φ p' ⋖ inl φ p) =>
      ⟨P.orient (inl_covBy_inl_iff.1 h), (isOut_inl_inl_iff _).symm⟩
    | .inr q, .inr q' => fun (h : inr φ q' ⋖ inr φ q) =>
      ⟨Q.orient (inr_covBy_inr_iff.1 h), (isOut_inr_inr_iff _).symm⟩
    | .inl p, .inr q => fun (h : inr φ q ⋖ inl φ p) =>
      have e : inr φ q = inl φ ((φ.inv ⟨q, (inr_le_inl_iff.1 h.le).fst⟩ : P.restrict S) : P) :=
        inr_eq_inl_of_mem _
      have hc : ((φ.inv ⟨q, (inr_le_inl_iff.1 h.le).fst⟩ : P.restrict S) : P) ⋖ p :=
        inl_covBy_inl_iff.1 (by rwa [← e])
      ⟨P.orient hc, (isOut_inl_inl_iff hc).symm.trans
        (Iff.of_eq (congrArg (IsOut φ (inl φ p)) e)).symm⟩
    | .inr q, .inl p => fun (h : inl φ p ⋖ inr φ q) =>
      have e : inl φ p = inr φ ((φ.hom ⟨p, (inl_le_inr_iff.1 h.le).fst⟩ : Q.restrict T) : Q) :=
        inl_eq_inr_of_mem _
      have hc : ((φ.hom ⟨p, (inl_le_inr_iff.1 h.le).fst⟩ : Q.restrict T) : Q) ⋖ q :=
        inr_covBy_inr_iff.1 (by rwa [← e])
      ⟨Q.orient hc, (isOut_inr_inr_iff hc).symm.trans
        (Iff.of_eq (congrArg (IsOut φ (inr φ q)) e)).symm⟩

variable (φ) in
protected def orient {x y : GlueCarrier φ} (h : y ⋖ x) : Bool :=
  (GlueCarrier.orientData φ x y h).1

theorem orient_eq_true_iff {x y : GlueCarrier φ} (h : y ⋖ x) :
    GlueCarrier.orient φ h = true ↔ IsOut φ x y :=
  (GlueCarrier.orientData φ x y h).2

theorem orient_inl {p p' : P} (h : p' ⋖ p) :
    GlueCarrier.orient φ ((inlSeg φ).apply_covBy_apply_iff.2 h) = P.orient h := by
  rw [Bool.eq_iff_iff, orient_eq_true_iff, inlSeg_apply, inlSeg_apply, isOut_inl_inl_iff h]

theorem orient_inr {q q' : Q} (h : q' ⋖ q) :
    GlueCarrier.orient φ ((inrSeg φ).apply_covBy_apply_iff.2 h) = Q.orient h := by
  rw [Bool.eq_iff_iff, orient_eq_true_iff, inrSeg_apply, inrSeg_apply, isOut_inr_inr_iff h]

end GlueCarrier

variable {φ}

variable (φ) in
@[implicit_reducible] def glue : OGP.{u} where
  carrier := GlueCarrier φ
  orient h := GlueCarrier.orient φ h

variable (φ) in
def glue.inl : P ⟶ glue φ :=
  ConcreteCategory.ofHom ⟨GlueCarrier.inlSeg φ,
    .of_initialSeg (Q := glue φ) (GlueCarrier.inlSeg φ) GlueCarrier.orient_inl⟩

variable (φ) in
def glue.inr : Q ⟶ glue φ :=
  ConcreteCategory.ofHom ⟨GlueCarrier.inrSeg φ,
    .of_initialSeg (Q := glue φ) (GlueCarrier.inrSeg φ) GlueCarrier.orient_inr⟩

@[simp] theorem glue.inl_apply (p : P) : glue.inl φ p = GlueCarrier.inl φ p := rfl

@[simp] theorem glue.inr_apply (q : Q) : glue.inr φ q = GlueCarrier.inr φ q := rfl

instance : IsInclusion (glue.inl φ) := ⟨GlueCarrier.inl_injective⟩

instance : IsInclusion (glue.inr φ) := ⟨GlueCarrier.inr_injective⟩

variable (φ) in
@[reassoc] theorem glue.condition : incl S ≫ glue.inl φ = (φ.hom ≫ incl T) ≫ glue.inr φ := by
  ext s
  exact GlueCarrier.inl_eq_inr_of_mem s.2

theorem glue.exists_inl_or_inr (x : glue φ) :
    (∃ p, glue.inl φ p = x) ∨ ∃ q, glue.inr φ q = x :=
  GlueCarrier.exists_inl_or_inr x

theorem glue.inl_eq_inr_iff {p : P} {q : Q} :
    glue.inl φ p = glue.inr φ q ↔ ∃ h : p ∈ S, ((φ.hom ⟨p, h⟩ : Q.restrict T) : Q) = q :=
  GlueCarrier.inl_eq_inr_iff

variable (φ) in
theorem glue.map_inl_sup_map_inr : map (glue.inl φ) ⊤ ⊔ map (glue.inr φ) ⊤ = ⊤ :=
  top_unique fun x _ => LowerSet.mem_sup_iff.2 <| (glue.exists_inl_or_inr x).imp
    (fun ⟨p, hp⟩ => ⟨p, trivial, hp⟩) fun ⟨q, hq⟩ => ⟨q, trivial, hq⟩

variable (φ) in
theorem glue.map_inl_inf_map_inr :
    map (glue.inl φ) ⊤ ⊓ map (glue.inr φ) ⊤ = map (incl S ≫ glue.inl φ) ⊤ := by
  refine SetLike.ext fun x => ?_
  rw [LowerSet.mem_inf_iff]
  constructor
  · rintro ⟨⟨p, -, hp⟩, ⟨q, -, hq⟩⟩
    obtain ⟨h, -⟩ := glue.inl_eq_inr_iff.1 (hp.trans hq.symm)
    exact ⟨⟨p, h⟩, trivial, hp⟩
  · rintro ⟨s, -, rfl⟩
    exact ⟨⟨s, trivial, rfl⟩, ⟨_, trivial, (GlueCarrier.inl_eq_inr_of_mem s.2).symm⟩⟩

section Desc

variable {W : OGP.{u}} (f : P ⟶ W) (g : Q ⟶ W) (w : incl S ≫ f = (φ.hom ≫ incl T) ≫ g)

private def descFun : glue φ → W :=
  Quot.lift (Sum.elim f g) (by
    rintro _ _ ⟨s⟩
    exact congrArg (fun h : P.restrict S ⟶ W => h s) w)

private theorem descFun_inl (p : P) : descFun f g w (glue.inl φ p) = f p := rfl

private theorem descFun_inr (q : Q) : descFun f g w (glue.inr φ q) = g q := rfl

def glue.desc : glue φ ⟶ W :=
  ConcreteCategory.ofHom ⟨descFun f g w, .of_forall_exists fun x => by
    rcases glue.exists_inl_or_inr x with ⟨p, rfl⟩ | ⟨q, rfl⟩
    · refine ⟨P, glue.inl φ, p, isMorphism _, ?_, rfl⟩
      convert isMorphism f using 1
      exact funext (descFun_inl f g w)
    · refine ⟨Q, glue.inr φ, q, isMorphism _, ?_, rfl⟩
      convert isMorphism g using 1
      exact funext (descFun_inr f g w)⟩

@[reassoc (attr := simp)] theorem glue.inl_desc : glue.inl φ ≫ glue.desc f g w = f := by
  ext p
  exact descFun_inl f g w p

@[reassoc (attr := simp)] theorem glue.inr_desc : glue.inr φ ≫ glue.desc f g w = g := by
  ext q
  exact descFun_inr f g w q

end Desc

@[ext] theorem glue.hom_ext {W : OGP.{u}} {m m' : glue φ ⟶ W}
    (hl : glue.inl φ ≫ m = glue.inl φ ≫ m') (hr : glue.inr φ ≫ m = glue.inr φ ≫ m') :
    m = m' := by
  ext x
  rcases glue.exists_inl_or_inr x with ⟨p, rfl⟩ | ⟨q, rfl⟩
  · exact congrArg (fun h : P ⟶ W => h p) hl
  · exact congrArg (fun h : Q ⟶ W => h q) hr

variable (φ) in
theorem isPushout_glue : IsPushout (incl S) (φ.hom ≫ incl T) (glue.inl φ) (glue.inr φ) :=
  .of_isColimit' ⟨glue.condition φ⟩ (PushoutCocone.IsColimit.mk _
    (fun s => glue.desc s.inl s.inr s.condition) (fun _ => glue.inl_desc ..)
    (fun _ => glue.inr_desc ..) fun _ _ hl hr => glue.hom_ext
      (hl.trans (glue.inl_desc ..).symm) (hr.trans (glue.inr_desc ..).symm))

variable (φ) in
theorem isPullback_glue : IsPullback (incl S) (φ.hom ≫ incl T) (glue.inl φ) (glue.inr φ) := by
  have hs (s : PullbackCone (glue.inl φ) (glue.inr φ)) (x : s.pt) :
      ∃ h : s.fst x ∈ S, ((φ.hom ⟨s.fst x, h⟩ : Q.restrict T) : Q) = s.snd x := by
    refine glue.inl_eq_inr_iff.1 ?_
    rw [← ConcreteCategory.comp_apply, s.condition, ConcreteCategory.comp_apply]
  let lift (s : PullbackCone (glue.inl φ) (glue.inr φ)) : s.pt ⟶ P.restrict S :=
    ConcreteCategory.ofHom ⟨fun x => ⟨s.fst x, (hs s x).fst⟩,
      .of_comp_of_injective (isMorphism (incl S)) IsInclusion.injective (isMorphism s.fst)⟩
  refine .of_isLimit' ⟨glue.condition φ⟩ (PullbackCone.IsLimit.mk _ lift
    (fun s => ?_) (fun s => ?_) fun s m hm _ => ?_)
  · ext x
    rfl
  · ext x
    exact (hs s x).snd
  · ext x
    exact ConcreteCategory.congr_hom hm x

theorem isPushout_of_cover {W : OGP.{u}} (f : P ⟶ W) (g : Q ⟶ W) [IsInclusion f]
    [IsInclusion g] (w : incl S ≫ f = (φ.hom ≫ incl T) ≫ g) (hsup : map f ⊤ ⊔ map g ⊤ = ⊤)
    (hinf : map f ⊤ ⊓ map g ⊤ = map (incl S ≫ f) ⊤) : IsPushout (incl S) (φ.hom ≫ incl T) f g := by
  have hd {p : P} {q : Q} (h : f p = g q) : glue.inl φ p = glue.inr φ q := by
    obtain ⟨s, -, hs⟩ : f p ∈ map (incl S ≫ f) ⊤ := hinf ▸ ⟨⟨p, trivial, rfl⟩, ⟨q, trivial, h.symm⟩⟩
    rw [ConcreteCategory.comp_apply] at hs
    obtain rfl := IsInclusion.injective (f := f) hs
    rw [← ConcreteCategory.comp_apply, w, ConcreteCategory.comp_apply] at h
    rw [← IsInclusion.injective (f := g) h, ← ConcreteCategory.comp_apply, glue.condition,
      ConcreteCategory.comp_apply]
  have hl (p : P) : glue.desc f g w (glue.inl φ p) = f p := by
    rw [← ConcreteCategory.comp_apply, glue.inl_desc]
  have hr (q : Q) : glue.desc f g w (glue.inr φ q) = g q := by
    rw [← ConcreteCategory.comp_apply, glue.inr_desc]
  have : IsIso (glue.desc f g w) := by
    refine (isIso_iff_bijective _).2 ⟨fun x x' h => ?_, fun y => ?_⟩
    · rcases glue.exists_inl_or_inr x with ⟨p, rfl⟩ | ⟨q, rfl⟩ <;>
        rcases glue.exists_inl_or_inr x' with ⟨p', rfl⟩ | ⟨q', rfl⟩
      · rw [hl, hl] at h
        rw [IsInclusion.injective h]
      · rw [hl, hr] at h
        exact hd h
      · rw [hr, hl] at h
        exact (hd h.symm).symm
      · rw [hr, hr] at h
        rw [IsInclusion.injective h]
    · have hy : y ∈ map f ⊤ ⊔ map g ⊤ := hsup ▸ trivial
      rcases LowerSet.mem_sup_iff.1 hy with ⟨p, -, rfl⟩ | ⟨q, -, rfl⟩
      · exact ⟨_, hl p⟩
      · exact ⟨_, hr q⟩
  exact (isPushout_glue φ).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (asIso (glue.desc f g w)) (by simp) (by simp) (by simp) (by simp)

section Pasting

variable (U V : OGP.{u}) (k : ℕ)
  (ψ : U.restrict (U.boundary ⊤ k true) ≅ V.restrict (V.boundary ⊤ k false))

theorem isPastingIn_glue :
    (glue ψ).IsPastingIn k (map (glue.inl ψ) ⊤) (map (glue.inr ψ) ⊤) ⊤ where
  sup_eq := glue.map_inl_sup_map_inr ψ
  inf_eq_output := by rw [glue.map_inl_inf_map_inr, map_comp, map_incl_top, map_boundary]
  inf_eq_input := by
    rw [glue.map_inl_inf_map_inr, glue.condition, map_comp, map_comp, map_top_of_isIso,
      map_incl_top, map_boundary]

variable {U V}

theorem isMolecule_glue (hU : IsMolecule U) (hV : IsMolecule V) : IsMolecule (glue ψ) :=
  (isPastingIn_glue U V k ψ).isMoleculeIn ((isMoleculeIn_map_iff _ ⊤).2 hU)
    ((isMoleculeIn_map_iff _ ⊤).2 hV)

variable (U V)

theorem isPasting_glue : IsPasting U V k (glue ψ) :=
  ⟨_, _, inferInstance, inferInstance, isPastingIn_glue U V k ψ⟩

end Pasting

end Atoms.Molecule.OGP
