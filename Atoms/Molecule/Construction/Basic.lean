import Atoms.ForMathlib.Data.FinEnum.Option
import Atoms.ForMathlib.Order.Basic
import Atoms.Molecule.Submolecule

universe u

open Order Set

namespace Atoms.Molecule.OGP

def point : OGP.{u} where
  carrier := PUnit.{u + 1}
  orient h := (h.ne (Subsingleton.elim _ _)).elim

transfer_instances point with OrderTop FinEnum DecidableLE

theorem isMin_point (x : point.{u}) : IsMin x :=
  fun _ _ => le_rfl

theorem isAtom_point : point.{u}.IsAtom := by
  have h : (⊤ : LowerSet point.{u}) = LowerSet.Iic ⊤ := LowerSet.Iic_top.symm
  refine ⟨?_, ⊤, h⟩
  rw [h]
  exact .point _ (isMin_point ⊤)

inductive SuspCarrier (X : Type u) : Type u
  | pole (α : Bool)
  | susp (x : X)
  deriving DecidableEq

namespace SuspCarrier

variable {X : Type u} [PartialOrder X]

protected def le : SuspCarrier X → SuspCarrier X → Prop
  | pole α, pole β => α = β
  | pole _, susp _ => True
  | susp _, pole _ => False
  | susp x, susp y => x ≤ y

instance : PartialOrder (SuspCarrier X) where
  le := SuspCarrier.le
  le_refl x := by
    cases x
    exacts [rfl, le_refl (α := X) _]
  le_trans x y z := by
    rcases x with α | x <;> rcases y with β | y <;> rcases z with γ | z
    all_goals intro h h'; first
      | exact (h : False).elim
      | exact (h' : False).elim
      | trivial
      | exact (h : α = β).trans h'
      | exact le_trans (α := X) h h'
  le_antisymm x y := by
    rcases x with α | x <;> rcases y with β | y
    all_goals intro h h'; first
      | exact (h : False).elim
      | exact (h' : False).elim
      | exact congrArg pole h
      | exact congrArg susp (le_antisymm (α := X) h h')

@[simp] theorem pole_le_pole {α β : Bool} : (pole α : SuspCarrier X) ≤ pole β ↔ α = β :=
  Iff.rfl

@[simp] theorem pole_le_susp (α : Bool) (x : X) : (pole α : SuspCarrier X) ≤ susp x :=
  trivial

@[simp] theorem not_susp_le_pole (x : X) (α : Bool) : ¬ (susp x : SuspCarrier X) ≤ pole α :=
  id

@[simp] theorem susp_le_susp {x y : X} : (susp x : SuspCarrier X) ≤ susp y ↔ x ≤ y :=
  Iff.rfl

@[simp] theorem susp_lt_susp {x y : X} : (susp x : SuspCarrier X) < susp y ↔ x < y := by
  simp only [lt_iff_le_not_ge, susp_le_susp]

theorem pole_lt_susp (α : Bool) (x : X) : (pole α : SuspCarrier X) < susp x :=
  lt_of_le_not_ge (pole_le_susp α x) (not_susp_le_pole x α)

theorem isMin_pole (α : Bool) : IsMin (pole α : SuspCarrier X) := by
  rintro (β | y) h
  · exact (h : β = α).symm
  · exact (not_susp_le_pole y α h).elim

theorem pole_covBy_susp {α : Bool} {x : X} : (pole α : SuspCarrier X) ⋖ susp x ↔ IsMin x := by
  refine ⟨fun h y hy => ?_, fun hx => ⟨pole_lt_susp α x, fun c hc hcx => ?_⟩⟩
  · by_contra hxy
    exact h.2 (pole_lt_susp α y) (susp_lt_susp.2 (lt_of_le_not_ge hy hxy))
  · rcases c with β | y
    · exact (isMin_pole β).not_lt hc
    · exact hx.not_lt (susp_lt_susp.1 hcx)

theorem susp_covBy_susp {x y : X} : (susp x : SuspCarrier X) ⋖ susp y ↔ x ⋖ y := by
  refine ⟨fun h => ⟨susp_lt_susp.1 h.1, fun c hxc hcy => h.2 (susp_lt_susp.2 hxc)
    (susp_lt_susp.2 hcy)⟩, fun h => ⟨susp_lt_susp.2 h.1, fun c hxc hcy => ?_⟩⟩
  rcases c with β | z
  · exact (isMin_pole β).not_lt hxc
  · exact h.2 (susp_lt_susp.1 hxc) (susp_lt_susp.1 hcy)

theorem not_covBy_pole {x : SuspCarrier X} {α : Bool} : ¬ x ⋖ pole α :=
  fun h => (isMin_pole α).not_lt h.lt

private def toWithBot : SuspCarrier X → WithBot X
  | pole _ => ⊥
  | susp x => x

private theorem strictMono_toWithBot : StrictMono (toWithBot : SuspCarrier X → WithBot X) := by
  rintro (α | x) (β | y) h
  · exact ((isMin_pole β).not_lt h).elim
  · exact WithBot.bot_lt_coe y
  · exact ((isMin_pole β).not_lt (h.trans' (pole_lt_susp false x))).elim
  · exact WithBot.coe_lt_coe.2 (susp_lt_susp.1 h)

private theorem toWithBot_covBy {a b : SuspCarrier X} (h : a ⋖ b) : toWithBot a ⋖ toWithBot b := by
  rcases a with α | x <;> rcases b with β | y
  · exact (not_covBy_pole h).elim
  · exact WithBot.bot_covBy_coe.2 (pole_covBy_susp.1 h)
  · exact (not_covBy_pole h).elim
  · exact WithBot.coe_covBy_coe.2 (susp_covBy_susp.1 h)

instance [GradeMinOrder ℕ X] : GradeMinOrder ℕ (SuspCarrier X) :=
  GradeMinOrder.liftRight toWithBot strictMono_toWithBot (fun _ _ => toWithBot_covBy) (by
    rintro (α | x) h
    · exact isMin_bot
    · exact absurd (h (pole_lt_susp false x).le) (not_susp_le_pole x false))

@[simp] theorem grade_pole [GradeMinOrder ℕ X] (α : Bool) : grade ℕ (pole α : SuspCarrier X) = 0 :=
  rfl

@[simp] theorem grade_susp [GradeMinOrder ℕ X] (x : X) :
    grade ℕ (susp x : SuspCarrier X) = grade ℕ x + 1 :=
  rfl

instance [OrderTop X] : OrderTop (SuspCarrier X) where
  top := susp ⊤
  le_top
    | pole _ => trivial
    | susp x => le_top (a := x)

instance [DecidableLE X] : DecidableLE (SuspCarrier X) := fun x y => match x, y with
  | pole α, pole β => inferInstanceAs (Decidable (α = β))
  | pole _, susp _ => isTrue trivial
  | susp _, pole _ => isFalse id
  | susp x, susp y => inferInstanceAs (Decidable (x ≤ y))

instance [FinEnum X] : FinEnum (SuspCarrier X) :=
  FinEnum.ofNodupList (pole false :: pole true :: (FinEnum.toList X).map susp)
    (by rintro ((_ | _) | x) <;> simp)
    (by simpa using (FinEnum.nodup_toList (α := X)).map (fun _ _ => susp.inj))

scoped instance : TopologicalSpace (SuspCarrier X) := Topology.upperSet (SuspCarrier X)

scoped instance : Topology.IsUpperSet (SuspCarrier X) := ⟨rfl⟩

protected def orient (P : OGP.{u}) : ∀ x y : SuspCarrier P, y ⋖ x → Bool
  | susp _, susp _, h => P.orient (susp_covBy_susp.1 h)
  | susp _, pole α, _ => α
  | pole _, _, h => (not_covBy_pole h).elim

end SuspCarrier

open SuspCarrier

abbrev suspension (P : OGP.{u}) : OGP.{u} where
  carrier := SuspCarrier P
  orient {x y} h := SuspCarrier.orient P x y h

variable {P : OGP.{u}}

theorem pole_mem_faces_suspension {α β : Bool} {x : P} :
    (pole β : suspension P) ∈ (suspension P).faces α (susp x) ↔ IsMin x ∧ β = α := by
  exact ⟨fun ⟨h, hβ⟩ => ⟨pole_covBy_susp.1 h, hβ⟩, fun ⟨hx, hβ⟩ => ⟨pole_covBy_susp.2 hx, hβ⟩⟩

theorem susp_mem_faces_suspension {α : Bool} {x y : P} :
    (susp y : suspension P) ∈ (suspension P).faces α (susp x) ↔ y ∈ P.faces α x :=
  ⟨fun ⟨h, ho⟩ => ⟨susp_covBy_susp.1 h, ho⟩, fun ⟨h, ho⟩ => ⟨susp_covBy_susp.2 h, ho⟩⟩

@[simp] theorem faces_suspension_pole (α β : Bool) :
    (suspension P).faces α (pole β) = ∅ :=
  eq_empty_of_forall_notMem fun _ h => not_covBy_pole h.1

def orientBot (P : OGP.{u}) : ∀ x y : WithBot P, y ⋖ x → Bool
  | (_ : P), (_ : P), h => P.orient (WithBot.coe_covBy_coe.1 h)
  | (_ : P), ⊥, _ => true
  | ⊥, _, h => (not_lt_bot h.lt).elim

abbrev augmentation (P : OGP.{u}) : OGP.{u} where
  carrier := WithBot P
  orient {x y} h := orientBot P x y h

theorem coe_mem_faces_augmentation {α : Bool} {x y : P} :
    (y : WithBot P) ∈ (augmentation P).faces α (x : WithBot P) ↔ y ∈ P.faces α x :=
  ⟨fun ⟨h, ho⟩ => ⟨WithBot.coe_covBy_coe.1 h, ho⟩, fun ⟨h, ho⟩ => ⟨WithBot.coe_covBy_coe.2 h, ho⟩⟩

theorem bot_mem_faces_augmentation {α : Bool} {x : P} :
    (⊥ : WithBot P) ∈ (augmentation P).faces α (x : WithBot P) ↔ IsMin x ∧ α = true :=
  ⟨fun ⟨h, ho⟩ => ⟨WithBot.bot_covBy_coe.1 h, ho.symm⟩,
    fun ⟨hx, hα⟩ => ⟨WithBot.bot_covBy_coe.2 hx, hα.symm⟩⟩

@[simp] theorem faces_augmentation_bot (α : Bool) :
    (augmentation P).faces α (⊥ : WithBot P) = ∅ :=
  eq_empty_of_forall_notMem fun _ h => not_lt_bot h.1.lt

theorem IsMorphism.withBotMap {Q : OGP.{u}} {f : P → Q} (hf : IsMorphism f) :
    IsMorphism (P := augmentation P) (Q := augmentation Q) (WithBot.map f) where
  bijOn_faces x α := by
    induction x using WithBot.recBotCoe with
    | bot => simp only [WithBot.map_bot, faces_augmentation_bot, bijOn_empty_iff_left]
    | coe x =>
      have hmin : IsMin (f x) ↔ IsMin x := by
        rw [← grade_eq_zero_iff, ← grade_eq_zero_iff, hf.grade_eq]
      refine ⟨fun y hy => ?_, fun y hy y' hy' h => ?_, fun z hz => ?_⟩
      · induction y using WithBot.recBotCoe with
        | bot =>
          obtain ⟨hx, hα⟩ := bot_mem_faces_augmentation.1 hy
          exact bot_mem_faces_augmentation.2 ⟨hmin.2 hx, hα⟩
        | coe y =>
          exact coe_mem_faces_augmentation.2
            ((hf.bijOn_faces x α).mapsTo (coe_mem_faces_augmentation.1 hy))
      · induction y using WithBot.recBotCoe <;> induction y' using WithBot.recBotCoe
        · rfl
        · exact (WithBot.bot_ne_coe h).elim
        · exact (WithBot.coe_ne_bot h).elim
        · exact congrArg _ ((hf.bijOn_faces x α).injOn (coe_mem_faces_augmentation.1 hy)
            (coe_mem_faces_augmentation.1 hy') (WithBot.coe_injective h))
      · rw [WithBot.map_coe] at hz
        induction z using WithBot.recBotCoe with
        | bot =>
          obtain ⟨hx, hα⟩ := bot_mem_faces_augmentation.1 hz
          exact ⟨⊥, bot_mem_faces_augmentation.2 ⟨hmin.1 hx, hα⟩, rfl⟩
        | coe z =>
          obtain ⟨y, hy, rfl⟩ := (hf.bijOn_faces x α).surjOn (coe_mem_faces_augmentation.1 hz)
          exact ⟨y, coe_mem_faces_augmentation.2 hy, rfl⟩

abbrev dual (P : OGP.{u}) (J : ℕ → Bool) : OGP.{u} where
  carrier := P
  orient {x _} h := xor (J (grade ℕ x)) (P.orient h)

@[simp] theorem faces_dual (J : ℕ → Bool) (α : Bool) (x : P) :
    (dual P J).faces α x = P.faces (xor (J (grade ℕ x)) α) x := by
  ext y
  refine exists_congr fun h => ?_
  change xor (J (grade ℕ x)) (P.orient h) = α ↔ P.orient h = xor (J (grade ℕ x)) α
  cases J (grade ℕ x) <;> cases P.orient h <;> cases α <;> decide

abbrev grayProduct (P Q : OGP.{u}) : OGP.{u} where
  carrier := P × Q
  orient {p q} h := if hg : grade ℕ q.1 = grade ℕ p.1 then
      xor (grade ℕ p.1).bodd (Q.orient (Prod.snd_covBy_snd_of_grade_eq h hg))
    else P.orient (Prod.fst_covBy_fst_of_grade_ne h hg)

theorem mem_faces_grayProduct {Q : OGP.{u}} {α : Bool} {p q : grayProduct P Q} :
    q ∈ (grayProduct P Q).faces α p ↔ q.1 ∈ P.faces α p.1 ∧ q.2 = p.2 ∨
      q.1 = p.1 ∧ q.2 ∈ Q.faces (xor (grade ℕ p.1).bodd α) p.2 := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨x', y'⟩
  constructor
  · rintro ⟨h, ho⟩
    change (if hg : _ then _ else _) = α at ho
    rcases Prod.covBy_iff.1 h with ⟨hx, rfl⟩ | ⟨hy, rfl⟩
    · rw [dif_neg (grade_strictMono hx.lt).ne] at ho
      exact .inl ⟨⟨hx, ho⟩, rfl⟩
    · rw [dif_pos rfl] at ho
      refine .inr ⟨rfl, hy, ?_⟩
      rw [← ho]
      cases (grade ℕ x').bodd <;> cases Q.orient hy <;> rfl
  · rintro (⟨⟨hx, h⟩, rfl⟩ | ⟨rfl, hy, h⟩)
    · refine ⟨Prod.covBy_iff.2 (.inl ⟨hx, rfl⟩), ?_⟩
      change (if hg : _ then _ else _) = α
      rw [dif_neg (grade_strictMono hx.lt).ne]
      exact h
    · refine ⟨Prod.covBy_iff.2 (.inr ⟨hy, rfl⟩), ?_⟩
      change (if hg : _ then _ else _) = α
      rw [dif_pos rfl]
      change xor _ (Q.orient hy) = α
      rw [h]
      cases (grade ℕ x').bodd <;> cases α <;> rfl

def join (P Q : OGP.{u}) : OGP.{u} where
  carrier := {p : grayProduct (augmentation P) (augmentation Q) // p ≠ ⊥}
  orient h :=
    (grayProduct (augmentation P) (augmentation Q)).orient (Subtype.coe_covBy_coe_ne_bot.2 h)

theorem mem_faces_join {Q : OGP.{u}} {α : Bool} {p q : join P Q} :
    q ∈ (join P Q).faces α p ↔ q.1 ∈ (grayProduct (augmentation P) (augmentation Q)).faces α p.1 :=
  ⟨fun ⟨h, ho⟩ => ⟨Subtype.coe_covBy_coe_ne_bot.2 h, ho⟩,
    fun ⟨h, ho⟩ => ⟨Subtype.coe_covBy_coe_ne_bot.1 h, ho⟩⟩

variable (P Q : OGP.{u}) in
transfer_instances join P Q with FinEnum DecidableLE

@[implicit_reducible] def globe : ℕ → OGP.{u}
  | 0 => point
  | n + 1 => suspension (globe n)

transfer_instances globe with OrderTop

@[simp] theorem grade_top_globe : (n : ℕ) → grade ℕ (⊤ : globe.{u} n) = n
  | 0 => rfl
  | n + 1 => congrArg (· + 1) (grade_top_globe n)

theorem krullDim_globe (n : ℕ) : krullDim (globe.{u} n) = n := by
  refine le_antisymm (krullDim_le_coe_iff.2 fun x => ?_) ?_
  · simpa using grade_mono (𝕆 := ℕ) (le_top (a := x))
  · simpa using grade_le_krullDim (⊤ : globe.{u} n)

theorem susp_unit_eq_top_globe_one : (susp PUnit.unit : globe.{u} 1) = ⊤ :=
  rfl

private theorem top_globe_one : (⊤ : LowerSet (globe.{u} 1)) = LowerSet.Iic ⊤ :=
  LowerSet.Iic_top.symm

theorem bdry_globe_one (α : Bool) :
    (globe.{u} 1).bdry ⊤ α = LowerSet.Iic (α := globe.{u} 1) (.pole α) := by
  rw [top_globe_one, bdry_Iic]
  have h : (globe.{u} 1).faces α ⊤ = ({.pole α} : Set (globe.{u} 1)) := by
    ext z
    rw [mem_singleton_iff]
    rcases z with β | z
    · exact (pole_mem_faces_suspension (P := point)).trans
        ⟨fun h => congrArg pole h.2, fun h => ⟨isMin_point ⊤, pole.inj h⟩⟩
    · exact (susp_mem_faces_suspension (P := point)).trans
        (iff_of_false (fun h => h.1.lt.ne rfl) fun h => nomatch h)
  rw [h, lowerClosure_singleton]

theorem boundary_zero_globe_one (α : Bool) :
    (globe.{u} 1).boundary ⊤ 0 α = LowerSet.Iic (α := globe.{u} 1) (.pole α) := by
  rw [← bdry_globe_one, bdry_eq_boundary]
  rw [LowerSet.krullDim_top, krullDim_globe]
  rfl

theorem mem_bdryFull_globe_one {a : globe.{u} 1} :
    a ∈ (globe.{u} 1).bdryFull ⊤ ↔ ∃ α, a = pole α := by
  rw [bdryFull, LowerSet.mem_sup_iff, bdry_globe_one, bdry_globe_one, LowerSet.mem_Iic_iff,
    LowerSet.mem_Iic_iff, Bool.exists_bool]
  exact or_congr ⟨(isMin_pole (X := globe.{u} 0) false).eq_of_le, fun h => h ▸ le_rfl⟩
    ⟨(isMin_pole (X := globe.{u} 0) true).eq_of_le, fun h => h ▸ le_rfl⟩

def simplex : ℕ → OGP.{u}
  | 0 => point
  | n + 1 => join point (simplex n)

def cube : ℕ → OGP.{u}
  | 0 => point
  | n + 1 => grayProduct (globe 1) (cube n)

transfer_instances globe with FinEnum DecidableLE

transfer_instances simplex with FinEnum DecidableLE

transfer_instances cube with FinEnum DecidableLE

end Atoms.Molecule.OGP
