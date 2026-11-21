import Atoms.Molecule.Construction.JoinMap

universe u

open CategoryTheory Order Set

namespace Atoms.Molecule.OGP

variable (U V W : OGP.{u})

section Components

def joinBotFst {U V : OGP.{u}} (x : WithBot (join U V)) : WithBot U :=
  WithBot.recBotCoe ⊥ (fun q : join U V => q.1.1) x

def joinBotSnd {U V : OGP.{u}} (x : WithBot (join U V)) : WithBot V :=
  WithBot.recBotCoe ⊥ (fun q : join U V => q.1.2) x

def joinPairBot (a : WithBot U) (b : WithBot V) : WithBot (join U V) :=
  a.recBotCoe
    (b.recBotCoe ⊥ fun v =>
      WithBot.some (α := join U V)
        ⟨(⊥, v), fun h => WithBot.coe_ne_bot (congrArg Prod.snd h)⟩)
    fun u =>
      WithBot.some (α := join U V)
        ⟨(u, b), fun h => WithBot.coe_ne_bot (congrArg Prod.fst h)⟩

variable {U V}

@[simp] theorem joinBotFst_bot : joinBotFst (⊥ : WithBot (join U V)) = ⊥ := rfl

@[simp] theorem joinBotSnd_bot : joinBotSnd (⊥ : WithBot (join U V)) = ⊥ := rfl

@[simp] theorem joinBotFst_coe (q : join U V) :
    joinBotFst (q : WithBot (join U V)) = q.1.1 := rfl

@[simp] theorem joinBotSnd_coe (q : join U V) :
    joinBotSnd (q : WithBot (join U V)) = q.1.2 := rfl

@[simp] theorem joinPairBot_bot_bot : joinPairBot U V ⊥ ⊥ = ⊥ := rfl

@[simp] theorem joinPairBot_eq_bot_iff {a : WithBot U} {b : WithBot V} :
    joinPairBot U V a b = ⊥ ↔ a = ⊥ ∧ b = ⊥ := by
  induction a using WithBot.recBotCoe <;> induction b using WithBot.recBotCoe <;>
    simp only [joinPairBot, WithBot.recBotCoe_bot, WithBot.recBotCoe_coe,
      WithBot.coe_ne_bot, and_false, and_true, and_self, iff_false] <;> nofun

@[simp] theorem joinBotFst_joinPairBot (a : WithBot U) (b : WithBot V) :
    joinBotFst (joinPairBot U V a b) = a := by
  induction a using WithBot.recBotCoe <;> induction b using WithBot.recBotCoe <;> rfl

@[simp] theorem joinBotSnd_joinPairBot (a : WithBot U) (b : WithBot V) :
    joinBotSnd (joinPairBot U V a b) = b := by
  induction a using WithBot.recBotCoe <;> induction b using WithBot.recBotCoe <;> rfl

@[simp] theorem joinPairBot_joinBotFst_joinBotSnd (x : WithBot (join U V)) :
    joinPairBot U V (joinBotFst x) (joinBotSnd x) = x := by
  induction x using WithBot.recBotCoe with
  | bot => rfl
  | coe q =>
    obtain ⟨⟨a, b⟩, hab⟩ := q
    induction a using WithBot.recBotCoe <;> induction b using WithBot.recBotCoe <;>
      first | exact absurd rfl hab | rfl

theorem joinBot_eq_iff {x y : WithBot (join U V)} :
    x = y ↔ joinBotFst x = joinBotFst y ∧ joinBotSnd x = joinBotSnd y := by
  refine ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => ?_⟩
  rw [← joinPairBot_joinBotFst_joinBotSnd x, ← joinPairBot_joinBotFst_joinBotSnd y, h.1, h.2]

theorem joinBot_le_iff {x y : WithBot (join U V)} :
    x ≤ y ↔ joinBotFst x ≤ joinBotFst y ∧ joinBotSnd x ≤ joinBotSnd y := by
  induction x using WithBot.recBotCoe with
  | bot => simp
  | coe p =>
      induction y using WithBot.recBotCoe with
      | bot =>
          simp only [joinBotFst_coe, joinBotSnd_coe, joinBotFst_bot, joinBotSnd_bot, le_bot_iff]
          exact iff_of_false (by simp) fun h => p.2 (Prod.ext h.1 h.2)
      | coe q => simp only [WithBot.coe_le_coe, joinBotFst_coe, joinBotSnd_coe]; exact join_le_iff

theorem grade_joinBot (x : WithBot (join U V)) :
    grade ℕ x = grade ℕ (joinBotFst x) + grade ℕ (joinBotSnd x) := by
  induction x using WithBot.recBotCoe with
  | bot => rfl
  | coe p =>
      have := one_le_grade_add_grade p
      rw [WithBot.grade_coe, grade_join, joinBotFst_coe, joinBotSnd_coe]
      omega

theorem mem_faces_augmentation_join {x y : WithBot (join U V)} {α : Bool} :
    y ∈ (augmentation (join U V)).faces α x ↔
      (joinBotFst y, joinBotSnd y) ∈
        (grayProduct (augmentation U) (augmentation V)).faces α (joinBotFst x, joinBotSnd x) := by
  induction x using WithBot.recBotCoe with
  | bot =>
    rw [faces_augmentation_bot, joinBotFst_bot, joinBotSnd_bot, mem_faces_grayProduct,
      faces_augmentation_bot, faces_augmentation_bot]
    simp
  | coe p =>
    induction y using WithBot.recBotCoe with
    | coe q => exact coe_mem_faces_augmentation.trans mem_faces_join
    | bot =>
      rw [bot_mem_faces_augmentation, ← grade_eq_zero_iff, grade_join, joinBotFst_bot,
        joinBotSnd_bot, joinBotFst_coe, joinBotSnd_coe, mem_faces_grayProduct]
      obtain ⟨⟨a, b⟩, hab⟩ := p
      induction a using WithBot.recBotCoe <;> induction b using WithBot.recBotCoe
      · exact absurd rfl hab
      · simpa [grade_eq_zero_iff] using bot_mem_faces_augmentation.symm
      · simpa [grade_eq_zero_iff] using bot_mem_faces_augmentation.symm
      · simp

theorem joinBotFst_map_joinMap {U' V' : OGP.{u}} (f : U → U') (g : V → V')
    (x : WithBot (join U V)) :
    joinBotFst (WithBot.map (joinMap f g) x) = WithBot.map f (joinBotFst x) := by
  induction x using WithBot.recBotCoe <;> rfl

theorem joinBotSnd_map_joinMap {U' V' : OGP.{u}} (f : U → U') (g : V → V')
    (x : WithBot (join U V)) :
    joinBotSnd (WithBot.map (joinMap f g) x) = WithBot.map g (joinBotSnd x) := by
  induction x using WithBot.recBotCoe <;> rfl

end Components

def joinLeftComponents (p : join (join U V) W) : WithBot U × WithBot V × WithBot W :=
  (joinBotFst p.1.1, joinBotSnd p.1.1, p.1.2)

def joinRightComponents (p : join U (join V W)) : WithBot U × WithBot V × WithBot W :=
  (p.1.1, joinBotFst p.1.2, joinBotSnd p.1.2)

theorem joinLeftComponents_injective : Function.Injective (joinLeftComponents U V W) := by
  intro p q h
  simp only [joinLeftComponents, Prod.mk.injEq] at h
  exact Subtype.ext (Prod.ext (joinBot_eq_iff.2 ⟨h.1, h.2.1⟩) h.2.2)

theorem joinRightComponents_injective : Function.Injective (joinRightComponents U V W) := by
  intro p q h
  simp only [joinRightComponents, Prod.mk.injEq] at h
  exact Subtype.ext (Prod.ext h.1 (joinBot_eq_iff.2 h.2))

def joinAssocFun (p : join (join U V) W) : join U (join V W) :=
  ⟨(joinBotFst p.1.1, joinPairBot V W (joinBotSnd p.1.1) p.1.2), fun h => by
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    obtain ⟨h2, h3⟩ := joinPairBot_eq_bot_iff.1 h2
    exact p.2 (Prod.ext (joinBot_eq_iff.2 ⟨h1, h2⟩) h3)⟩

def joinAssocInvFun (p : join U (join V W)) : join (join U V) W :=
  ⟨(joinPairBot U V p.1.1 (joinBotFst p.1.2), joinBotSnd p.1.2), fun h => by
    obtain ⟨h1, h3⟩ := Prod.mk.inj h
    obtain ⟨h1, h2⟩ := joinPairBot_eq_bot_iff.1 h1
    exact p.2 (Prod.ext h1 (joinBot_eq_iff.2 ⟨h2, h3⟩))⟩

theorem joinRightComponents_joinAssocFun (p : join (join U V) W) :
    joinRightComponents U V W (joinAssocFun U V W p) = joinLeftComponents U V W p := by
  simp [joinRightComponents, joinLeftComponents, joinAssocFun]

theorem joinLeftComponents_joinAssocInvFun (p : join U (join V W)) :
    joinLeftComponents U V W (joinAssocInvFun U V W p) = joinRightComponents U V W p := by
  simp [joinLeftComponents, joinRightComponents, joinAssocInvFun]

def joinAssocEquiv : join (join U V) W ≃ join U (join V W) where
  toFun := joinAssocFun U V W
  invFun := joinAssocInvFun U V W
  left_inv p := joinLeftComponents_injective U V W (by
    rw [joinLeftComponents_joinAssocInvFun, joinRightComponents_joinAssocFun])
  right_inv p := joinRightComponents_injective U V W (by
    rw [joinRightComponents_joinAssocFun, joinLeftComponents_joinAssocInvFun])

@[simp] theorem joinAssocFun_joinAssocInvFun (p : join U (join V W)) :
    joinAssocFun U V W (joinAssocInvFun U V W p) = p :=
  (joinAssocEquiv U V W).right_inv p

@[simp] theorem joinAssocInvFun_joinAssocFun (p : join (join U V) W) :
    joinAssocInvFun U V W (joinAssocFun U V W p) = p :=
  (joinAssocEquiv U V W).left_inv p

theorem joinLeft_le_iff {p q : join (join U V) W} :
    p ≤ q ↔ (joinLeftComponents U V W p).1 ≤ (joinLeftComponents U V W q).1 ∧
      (joinLeftComponents U V W p).2.1 ≤ (joinLeftComponents U V W q).2.1 ∧
      (joinLeftComponents U V W p).2.2 ≤ (joinLeftComponents U V W q).2.2 := by
  rw [join_le_iff, joinBot_le_iff, and_assoc]
  rfl

theorem joinRight_le_iff {p q : join U (join V W)} :
    p ≤ q ↔ (joinRightComponents U V W p).1 ≤ (joinRightComponents U V W q).1 ∧
      (joinRightComponents U V W p).2.1 ≤ (joinRightComponents U V W q).2.1 ∧
      (joinRightComponents U V W p).2.2 ≤ (joinRightComponents U V W q).2.2 := by
  rw [join_le_iff, joinBot_le_iff]
  rfl

private theorem xor_bodd_add (m n : ℕ) (α : Bool) :
    xor (m + n).bodd α = xor n.bodd (xor m.bodd α) := by
  rw [Nat.bodd_add, Bool.xor_comm m.bodd, Bool.xor_assoc]

theorem joinAssocFun_mem_faces_iff {U V W : OGP.{u}} {p q : join (join U V) W} {α : Bool} :
    joinAssocFun U V W q ∈ (join U (join V W)).faces α (joinAssocFun U V W p) ↔
      q ∈ (join (join U V) W).faces α p := by
  rw [mem_faces_join, mem_faces_grayProduct, mem_faces_augmentation_join, mem_faces_grayProduct,
    joinBot_eq_iff, mem_faces_join, mem_faces_grayProduct, mem_faces_augmentation_join,
    mem_faces_grayProduct, joinBot_eq_iff, grade_joinBot, xor_bodd_add]
  dsimp only [joinAssocFun]
  rw [joinBotFst_joinPairBot, joinBotSnd_joinPairBot, joinBotFst_joinPairBot,
    joinBotSnd_joinPairBot]
  tauto

def joinAssoc : join (join U V) W ≅ join U (join V W) where
  hom := ConcreteCategory.ofHom ⟨joinAssocFun U V W, ⟨fun p α =>
    ⟨fun _ h => joinAssocFun_mem_faces_iff.2 h, (joinAssocEquiv U V W).injective.injOn,
      fun z hz => ⟨joinAssocInvFun U V W z, joinAssocFun_mem_faces_iff.1
        (by rwa [joinAssocFun_joinAssocInvFun]),
        joinAssocFun_joinAssocInvFun U V W z⟩⟩⟩⟩
  inv := ConcreteCategory.ofHom ⟨joinAssocInvFun U V W, ⟨fun p α =>
    ⟨fun q h => joinAssocFun_mem_faces_iff.1
      (by rwa [joinAssocFun_joinAssocInvFun, joinAssocFun_joinAssocInvFun]),
      (joinAssocEquiv U V W).symm.injective.injOn,
      fun z hz => ⟨joinAssocFun U V W z,
        joinAssocFun_joinAssocInvFun U V W p ▸ joinAssocFun_mem_faces_iff.2 hz,
        joinAssocInvFun_joinAssocFun U V W z⟩⟩⟩⟩
  hom_inv_id := by ext p; exact joinAssocInvFun_joinAssocFun U V W p
  inv_hom_id := by ext p; exact joinAssocFun_joinAssocInvFun U V W p

theorem joinRightComponents_joinAssoc (p : join (join U V) W) :
    joinRightComponents U V W ((joinAssoc U V W).hom p) = joinLeftComponents U V W p :=
  joinRightComponents_joinAssocFun U V W p

theorem joinLeftComponents_joinMap {U' V' W' : OGP.{u}} (f : U → U') (g : V → V') (h : W → W')
    (p : join (join U V) W) :
    joinLeftComponents U' V' W' (joinMap (joinMap f g) h p) =
      (WithBot.map f (joinLeftComponents U V W p).1,
        WithBot.map g (joinLeftComponents U V W p).2.1,
        WithBot.map h (joinLeftComponents U V W p).2.2) := by
  simp only [joinLeftComponents, joinMap_val, joinBotFst_map_joinMap, joinBotSnd_map_joinMap]

theorem joinRightComponents_joinMap {U' V' W' : OGP.{u}} (f : U → U') (g : V → V') (h : W → W')
    (p : join U (join V W)) :
    joinRightComponents U' V' W' (joinMap f (joinMap g h) p) =
      (WithBot.map f (joinRightComponents U V W p).1,
        WithBot.map g (joinRightComponents U V W p).2.1,
        WithBot.map h (joinRightComponents U V W p).2.2) := by
  simp only [joinRightComponents, joinMap_val, joinBotFst_map_joinMap, joinBotSnd_map_joinMap]

theorem joinAssoc_joinMap {U' V' W' : OGP.{u}} (f : U → U') (g : V → V') (h : W → W')
    (p : join (join U V) W) :
    (joinAssoc U' V' W').hom (joinMap (joinMap f g) h p) =
      joinMap f (joinMap g h) ((joinAssoc U V W).hom p) := by
  apply joinRightComponents_injective
  rw [joinRightComponents_joinAssoc, joinLeftComponents_joinMap, joinRightComponents_joinMap,
    joinRightComponents_joinAssoc]

end Atoms.Molecule.OGP
