import PauliJung.Models

/-!
# Ten canonical cases
-/

namespace PauliJung

/-! ## Ten canonical cases

Each case is a small world with named states. Causation is a finite list of
edges, and a `side` labelling marks the causally sealed components.
`sep_tac` checks a separation claim by trying every pair of states.

Numbers in the statistical cases (April fish, Rhine, astrology) are **illustrative**,
chosen to show the structure of the argument, not historical data. -/

/-- Shared archetypes. -/
inductive Arch
  | rebirth | shadow | death | fire | series | fish | number | wholeness | psi | union
  deriving DecidableEq

/-- Exhaust all pairs of states: every causal edge stays inside one side. -/
macro "sep_tac" : tactic =>
  `(tactic| (intro x y h; rcases x with x | x <;> cases x <;> rcases y with y | y <;>
      cases y <;> first | rfl | exact absurd h (by decide)))

/-- Exhaust all pairs of states: a Boolean set is closed under direct causes. -/
macro "anc_tac" : tactic =>
  `(tactic| (intro a b h hb; rcases a with a | a <;> cases a <;> rcases b with b | b <;>
      cases b <;> first | rfl | exact absurd h (by decide) | exact absurd hb (by decide)))

/-- Exhaust all states: two Boolean sets are disjoint. -/
macro "dis_tac" : tactic =>
  `(tactic| (intro a ha hb; rcases a with a | a <;> cases a <;>
      first | exact absurd ha (by decide) | exact absurd hb (by decide)))

/-! ### 1. The golden scarab (Jung, c. 1920s)

A patient recounts a dream of a golden scarab; at that moment a scarab-like
beetle taps at the window. Jung perceives the beetle and catches it, which is
ordinary mind–matter causation. The recounting and the beetle's flight stay
causally sealed from each other. -/

inductive ScarabU | before | session deriving DecidableEq
inductive ScarabM | dreamsOfScarab | recountsDream | jungNotices deriving DecidableEq
inductive ScarabP | still | beetleFlies | beetleTaps | jungCatchesBeetle deriving DecidableEq

def scarabψ : ScarabU → ScarabM
  | .before => .dreamsOfScarab
  | .session => .recountsDream

def scarabφ : ScarabU → ScarabP
  | .before => .still
  | .session => .beetleTaps

def scarabEdge : Sum ScarabM ScarabP → Sum ScarabM ScarabP → Bool
  | .inl .dreamsOfScarab, .inl .recountsDream => true
  | .inr .beetleFlies, .inr .beetleTaps => true
  | .inr .beetleTaps, .inl .jungNotices => true
  | .inl .jungNotices, .inr .jungCatchesBeetle => true
  | _, _ => false

/-- `true`: the patient's psyche; `false`: the beetle and Jung's response. -/
def scarabSide : Sum ScarabM ScarabP → Bool
  | .inl .dreamsOfScarab | .inl .recountsDream => true
  | _ => false

@[reducible] def scarabW : Model where
  U := ScarabU
  M := ScarabM
  P := ScarabP
  A := Arch
  ψ := scarabψ
  φ := scarabφ
  causes := fun x y => scarabEdge x y = true
  constellated := fun a u => a = Arch.rebirth ∧ u = ScarabU.session
  expressesM := fun a m => a = Arch.rebirth ∧ m = ScarabM.recountsDream
  expressesP := fun a p => a = Arch.rebirth ∧ p = ScarabP.beetleTaps

theorem scarab_sync :
    Synchronicity scarabW ScarabM.recountsDream ScarabP.beetleTaps :=
  sync_of_separated scarabW scarabSide (by sep_tac) Arch.rebirth ScarabU.session
    ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (by decide)

/-- Mind–matter causation exists in this world (Jung perceives the beetle),
so the world is not parallelist, yet the synchronicity stands. -/
theorem scarab_has_perception :
    Path scarabW.causes (.inr ScarabP.beetleTaps) (.inl ScarabM.jungNotices) :=
  Path.single rfl

/-- **Refinement: the observer as common effect.** Jung both hears the dream
and sees the beetle; his recognition is a *collider*. -/
def scarabEdge2 (x y : Sum ScarabM ScarabP) : Bool :=
  scarabEdge x y ||
    match x, y with
    | .inl .recountsDream, .inl .jungNotices => true
    | _, _ => false

@[reducible] def scarabColliderW : Model :=
  { scarabW with causes := fun x y => scarabEdge2 x y = true }

/-- The causal past of the beetle's tapping. -/
def scarabPastP : Sum ScarabM ScarabP → Bool
  | .inr .beetleFlies | .inr .beetleTaps => true
  | _ => false

/-- Dream and beetle now have a common effect... -/
theorem scarab_collider_common_effect :
    Path scarabColliderW.causes (.inl ScarabM.recountsDream) (.inl ScarabM.jungNotices) ∧
    Path scarabColliderW.causes (.inr ScarabP.beetleTaps) (.inl ScarabM.jungNotices) :=
  ⟨Path.single rfl, Path.single rfl⟩

/-- ...so no division into sealed components can separate them... -/
theorem scarab_collider_not_separable {β : Type} (side : Sum ScarabM ScarabP → β)
    (h : ∀ x y, scarabColliderW.causes x y → side x = side y) :
    side (.inl ScarabM.recountsDream) = side (.inr ScarabP.beetleTaps) :=
  (h (.inl ScarabM.recountsDream) (.inl ScarabM.jungNotices) rfl).trans
    (h (.inr ScarabP.beetleTaps) (.inl ScarabM.jungNotices) rfl).symm

/-- ...and yet the synchronicity stands, because their causal pasts are
disjoint. Being noticed together does not link two events. -/
theorem scarab_collider_sync :
    Synchronicity scarabColliderW ScarabM.recountsDream ScarabP.beetleTaps :=
  sync_of_ancestral scarabColliderW scarabSide scarabPastP
    (by anc_tac) (by anc_tac) (by dis_tac) Arch.rebirth ScarabU.session
    ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ rfl rfl

/-- Lucadou's principle on the scarab: had the recounting been used to bring
the beetle about, the coincidence would keep its meaning and stop being a
synchronicity. -/
theorem scarab_exploited :
    MeaningfulCoincidence
        (scarabW.exploit ScarabM.recountsDream ScarabP.beetleTaps)
        ScarabM.recountsDream ScarabP.beetleTaps ∧
      ¬ Synchronicity (scarabW.exploit ScarabM.recountsDream ScarabP.beetleTaps)
        ScarabM.recountsDream ScarabP.beetleTaps :=
  lucadou scarabW scarab_sync

/-! ### 2. The Pauli effect (Göttingen)

An apparatus in James Franck's Göttingen laboratory failed; Pauli's train
had stopped at Göttingen at that time. The failure has a perfectly good
physical cause of its own. Synchronicity does not deny that, it only denies a
link to Pauli. -/

inductive PauliU | goettingen deriving DecidableEq
inductive PauliM | pauliOnTrain | franckPuzzled deriving DecidableEq
inductive PauliP | trainHalts | vacuumLeak | apparatusFails deriving DecidableEq

def pauliEdge : Sum PauliM PauliP → Sum PauliM PauliP → Bool
  | .inr .trainHalts, .inl .pauliOnTrain => true
  | .inr .vacuumLeak, .inr .apparatusFails => true
  | .inr .apparatusFails, .inl .franckPuzzled => true
  | _, _ => false

/-- `true`: Pauli and his train; `false`: Franck's laboratory. -/
def pauliSide : Sum PauliM PauliP → Bool
  | .inl .pauliOnTrain | .inr .trainHalts => true
  | _ => false

@[reducible] def pauliW : Model where
  U := PauliU
  M := PauliM
  P := PauliP
  A := Arch
  ψ := fun _ => PauliM.pauliOnTrain
  φ := fun _ => PauliP.apparatusFails
  causes := fun x y => pauliEdge x y = true
  constellated := fun a _ => a = Arch.shadow
  expressesM := fun a m => a = Arch.shadow ∧ m = PauliM.pauliOnTrain
  expressesP := fun a p => a = Arch.shadow ∧ p = PauliP.apparatusFails

theorem pauli_effect_sync :
    Synchronicity pauliW PauliM.pauliOnTrain PauliP.apparatusFails :=
  sync_of_separated pauliW pauliSide (by sep_tac) Arch.shadow PauliU.goettingen
    rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (by decide)

/-- The failure has its own physical cause. -/
theorem pauli_failure_has_cause :
    Path pauliW.causes (.inr PauliP.vacuumLeak) (.inr PauliP.apparatusFails) :=
  Path.single rfl

/-! ### 3. Birds at the death (Jung's patient's wife)

Birds had gathered at the deaths of the wife's mother and grandmother. During
her husband's treatment a flock settled on the house, and she grew alarmed;
meanwhile he collapsed in the street. The birds cause her alarm (perception),
but nothing links the alarm to the collapse. -/

inductive BirdsU | deathDay deriving DecidableEq
inductive BirdsM | wifeAlarmed deriving DecidableEq
inductive BirdsP | birdsGather | heartFails | husbandCollapses deriving DecidableEq

def birdsEdge : Sum BirdsM BirdsP → Sum BirdsM BirdsP → Bool
  | .inr .birdsGather, .inl .wifeAlarmed => true
  | .inr .heartFails, .inr .husbandCollapses => true
  | _, _ => false

/-- `true`: the house; `false`: the street. -/
def birdsSide : Sum BirdsM BirdsP → Bool
  | .inl .wifeAlarmed | .inr .birdsGather => true
  | _ => false

@[reducible] def birdsW : Model where
  U := BirdsU
  M := BirdsM
  P := BirdsP
  A := Arch
  ψ := fun _ => BirdsM.wifeAlarmed
  φ := fun _ => BirdsP.husbandCollapses
  causes := fun x y => birdsEdge x y = true
  constellated := fun a _ => a = Arch.death
  expressesM := fun a _ => a = Arch.death
  expressesP := fun a p => a = Arch.death ∧ p = BirdsP.husbandCollapses

theorem birds_sync :
    Synchronicity birdsW BirdsM.wifeAlarmed BirdsP.husbandCollapses :=
  sync_of_separated birdsW birdsSide (by sep_tac) Arch.death BirdsU.deathDay
    rfl rfl ⟨rfl, rfl⟩ (by decide)

/-! ### 4. Swedenborg's vision of the Stockholm fire (1759)

In Gothenburg, Swedenborg described a fire raging in Stockholm, about 400 km
away, as it happened. News arrived days later. The later confirmation is
causal; the vision was not. -/

inductive SwedU | evening1759 deriving DecidableEq
inductive SwedM | visionOfFire | tellsGuests | newsArrives deriving DecidableEq
inductive SwedP | fireStarts | fireSpreads | fireStops deriving DecidableEq

def swedEdge : Sum SwedM SwedP → Sum SwedM SwedP → Bool
  | .inl .visionOfFire, .inl .tellsGuests => true
  | .inr .fireStarts, .inr .fireSpreads => true
  | .inr .fireSpreads, .inr .fireStops => true
  | .inr .fireStops, .inl .newsArrives => true
  | _, _ => false

/-- `true`: Swedenborg's vision and its telling; `false`: the fire and its news. -/
def swedSide : Sum SwedM SwedP → Bool
  | .inl .visionOfFire | .inl .tellsGuests => true
  | _ => false

@[reducible] def swedW : Model where
  U := SwedU
  M := SwedM
  P := SwedP
  A := Arch
  ψ := fun _ => SwedM.visionOfFire
  φ := fun _ => SwedP.fireSpreads
  causes := fun x y => swedEdge x y = true
  constellated := fun a _ => a = Arch.fire
  expressesM := fun a m => a = Arch.fire ∧ m = SwedM.visionOfFire
  expressesP := fun a p => a = Arch.fire ∧ p = SwedP.fireSpreads

theorem swedenborg_sync :
    Synchronicity swedW SwedM.visionOfFire SwedP.fireSpreads :=
  sync_of_separated swedW swedSide (by sep_tac) Arch.fire SwedU.evening1759
    rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (by decide)

/-- The news, unlike the vision, is causally downstream of the fire. -/
theorem swedenborg_news_is_causal :
    Path swedW.causes (.inr SwedP.fireSpreads) (.inl SwedM.newsArrives) :=
  Path.tail (b := (Sum.inr SwedP.fireStops : Sum swedW.M swedW.P))
    (Path.single rfl) rfl

/-! ### 5. Monsieur de Fontgibu's plum pudding (Deschamps, via Flammarion)

As a boy, Émile Deschamps was given plum pudding by M. de Fontgibu. Years
later a Paris restaurant's last plum pudding had just gone to de Fontgibu.
Later still, at a dinner with plum pudding, Deschamps remarked that only de
Fontgibu was missing, and de Fontgibu walked in, having mistaken the address.

The boyhood gift is causal, so it is not a synchronicity. The two later
episodes are. The `series` archetype is sporadic. -/

inductive PuddingU | boyhood | restaurant | dinner deriving DecidableEq
inductive PuddingM | tastesPudding | ordersPudding | remarksAbsence deriving DecidableEq
inductive PuddingP
  | fontgibuGivesPudding | lastPuddingTaken | wrongAddress | fontgibuEnters
  deriving DecidableEq

def puddingψ : PuddingU → PuddingM
  | .boyhood => .tastesPudding
  | .restaurant => .ordersPudding
  | .dinner => .remarksAbsence

def puddingφ : PuddingU → PuddingP
  | .boyhood => .fontgibuGivesPudding
  | .restaurant => .lastPuddingTaken
  | .dinner => .fontgibuEnters

def puddingEdge : Sum PuddingM PuddingP → Sum PuddingM PuddingP → Bool
  | .inr .fontgibuGivesPudding, .inl .tastesPudding => true
  | .inr .wrongAddress, .inr .fontgibuEnters => true
  | _, _ => false

/-- `true`: Deschamps's world (including the boyhood gift that reached him);
`false`: de Fontgibu's independent doings. -/
def puddingSide : Sum PuddingM PuddingP → Bool
  | .inl _ => true
  | .inr .fontgibuGivesPudding => true
  | .inr _ => false

@[reducible] def puddingW : Model where
  U := PuddingU
  M := PuddingM
  P := PuddingP
  A := Arch
  ψ := puddingψ
  φ := puddingφ
  causes := fun x y => puddingEdge x y = true
  constellated := fun a u =>
    a = Arch.series ∧ (u = PuddingU.restaurant ∨ u = PuddingU.dinner)
  expressesM := fun a m =>
    a = Arch.series ∧ (m = PuddingM.ordersPudding ∨ m = PuddingM.remarksAbsence)
  expressesP := fun a p =>
    a = Arch.series ∧ (p = PuddingP.lastPuddingTaken ∨ p = PuddingP.fontgibuEnters)

theorem pudding_restaurant_sync :
    Synchronicity puddingW PuddingM.ordersPudding PuddingP.lastPuddingTaken :=
  sync_of_separated puddingW puddingSide (by sep_tac) Arch.series PuddingU.restaurant
    ⟨rfl, Or.inl rfl⟩ ⟨rfl, Or.inl rfl⟩ ⟨rfl, Or.inl rfl⟩ (by decide)

theorem pudding_dinner_sync :
    Synchronicity puddingW PuddingM.remarksAbsence PuddingP.fontgibuEnters :=
  sync_of_separated puddingW puddingSide (by sep_tac) Arch.series PuddingU.dinner
    ⟨rfl, Or.inr rfl⟩ ⟨rfl, Or.inr rfl⟩ ⟨rfl, Or.inr rfl⟩ (by decide)

/-- The boyhood gift is an ordinary cause, not a synchronicity. -/
theorem pudding_boyhood_not_sync :
    ¬ Synchronicity puddingW PuddingM.tastesPudding PuddingP.fontgibuGivesPudding :=
  fun h => h.2 (Or.inr (Or.inl (Path.single rfl)))

theorem pudding_series_sporadic : Sporadic puddingW Arch.series :=
  ⟨⟨PuddingU.restaurant, rfl, Or.inl rfl⟩, ⟨PuddingU.boyhood, by decide⟩⟩

/-! ### 6. The April-fish series (Jung, 1 April 1949)

Within about a day Jung met fish at lunch, the "April fish" joke, a fish
inscription, a patient's fish pictures, an embroidery of fish, and a
patient's fish dream. Each single encounter is ordinary perception, hence
causal. Whatever is remarkable lies in the *clustering*, and Jung himself
allowed that the run might be chance. The formal moral: the verdict depends
entirely on the chance baseline. -/

inductive FishU | lunch | inscription | pictures | embroidery deriving DecidableEq
inductive FishM | noticesFish deriving DecidableEq
inductive FishP | fishPresent deriving DecidableEq

def fishEdge : Sum FishM FishP → Sum FishM FishP → Bool
  | .inr .fishPresent, .inl .noticesFish => true
  | _, _ => false

@[reducible] def fishW : Model where
  U := FishU
  M := FishM
  P := FishP
  A := Arch
  ψ := fun _ => FishM.noticesFish
  φ := fun _ => FishP.fishPresent
  causes := fun x y => fishEdge x y = true
  constellated := fun a _ => a = Arch.fish
  expressesM := fun a _ => a = Arch.fish
  expressesP := fun a _ => a = Arch.fish

/-- No single fish encounter is a synchronicity: each is perceived. -/
theorem fish_not_sync_individually (u : FishU) :
    ¬ Synchronicity fishW (fishW.ψ u) (fishW.φ u) :=
  fun h => h.2 (Or.inr (Or.inl (Path.single rfl)))

/-- Six fish motifs among eight notable events of the day: remarkable against
a low baseline of 1 in 10... -/
theorem fish_run_low_baseline : AboveChance 6 8 1 10 := by decide

/-- ...and unremarkable against a high one of 3 in 4. -/
theorem fish_run_high_baseline : ¬ AboveChance 6 8 3 4 := by decide

/-! ### 7. Room 137 (Pauli, December 1958)

Pauli spent his career on the fine-structure constant, close to 1/137, and
died in room 137 of Zurich's Red Cross hospital. The `number` archetype is
lawlike, ordering his physics too, but there his knowledge is causal
(spectra are measured, then understood). Only the room is a synchronicity.
A lawlike archetype does not make every moment synchronistic. -/

inductive R137U | physicsYears | dec1958 deriving DecidableEq
inductive R137M | computesAlpha | preoccupiedWith137 deriving DecidableEq
inductive R137P | spectrumMeasured | illness | assignedRoom137 deriving DecidableEq

def r137ψ : R137U → R137M
  | .physicsYears => .computesAlpha
  | .dec1958 => .preoccupiedWith137

def r137φ : R137U → R137P
  | .physicsYears => .spectrumMeasured
  | .dec1958 => .assignedRoom137

def r137Edge : Sum R137M R137P → Sum R137M R137P → Bool
  | .inr .spectrumMeasured, .inl .computesAlpha => true
  | .inl .computesAlpha, .inl .preoccupiedWith137 => true
  | .inr .illness, .inr .assignedRoom137 => true
  | _, _ => false

/-- `true`: Pauli's physics and mind; `false`: the hospital. -/
def r137Side : Sum R137M R137P → Bool
  | .inl _ => true
  | .inr .spectrumMeasured => true
  | .inr _ => false

@[reducible] def room137W : Model where
  U := R137U
  M := R137M
  P := R137P
  A := Arch
  ψ := r137ψ
  φ := r137φ
  causes := fun x y => r137Edge x y = true
  constellated := fun a _ => a = Arch.number
  expressesM := fun a m => a = Arch.number ∧ m = R137M.preoccupiedWith137
  expressesP := fun a p => a = Arch.number ∧ p = R137P.assignedRoom137

theorem room137_sync :
    Synchronicity room137W R137M.preoccupiedWith137 R137P.assignedRoom137 :=
  sync_of_separated room137W r137Side (by sep_tac) Arch.number R137U.dec1958
    rfl ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ (by decide)

theorem alpha_work_not_sync :
    ¬ Synchronicity room137W R137M.computesAlpha R137P.spectrumMeasured :=
  fun h => h.2 (Or.inr (Or.inl (Path.single rfl)))

theorem number_lawlike : Lawlike room137W Arch.number := fun _ => rfl

/-- Lawlike orderedness, yet a moment that is not a synchronicity. -/
theorem lawlike_not_everywhere_sync :
    Lawlike room137W Arch.number ∧
      ∃ u, ¬ Synchronicity room137W (room137W.ψ u) (room137W.φ u) :=
  ⟨number_lawlike, R137U.physicsYears, alpha_work_not_sync⟩

/-! ### 8. The I Ching consultation (Jung's foreword, 1949)

Jung asked the I Ching about the planned English edition and obtained
hexagram 50, *The Caldron*. Asking causes the toss, and the toss causes the
outcome, so under the strict definition this is **not** a synchronicity.
Jung's claim is subtler: the *content* of the question does not raise the
chance of the fitting hexagram. That is a statement about frequencies across
consultations, checked below. This case shows where the strict definition is
too coarse. -/

inductive IChingU | consultation deriving DecidableEq
inductive IChingM | asksAboutBook deriving DecidableEq
inductive IChingP | coinsTossed | hexagram50 deriving DecidableEq

def ichingEdge : Sum IChingM IChingP → Sum IChingM IChingP → Bool
  | .inl .asksAboutBook, .inr .coinsTossed => true
  | .inr .coinsTossed, .inr .hexagram50 => true
  | _, _ => false

@[reducible] def ichingW : Model where
  U := IChingU
  M := IChingM
  P := IChingP
  A := Arch
  ψ := fun _ => IChingM.asksAboutBook
  φ := fun _ => IChingP.hexagram50
  causes := fun x y => ichingEdge x y = true
  constellated := fun a _ => a = Arch.wholeness
  expressesM := fun a _ => a = Arch.wholeness
  expressesP := fun a _ => a = Arch.wholeness

theorem iching_not_strict_sync :
    ¬ Synchronicity ichingW IChingM.asksAboutBook IChingP.hexagram50 :=
  fun h => h.2 (Or.inl
    (Path.tail (b := (Sum.inr IChingP.coinsTossed : Sum ichingW.M ichingW.P))
      (Path.single rfl) rfl))

/-- Consultations as (question, hexagram) codes: question 0 is "about the
book", hexagram 50 is *The Caldron*. -/
def consultations : List (Nat × Nat) := [(0, 50), (0, 1), (1, 50), (1, 1)]

/-- Question content and hexagram are uncorrelated (2·2 = 1·4). -/
theorem iching_content_independent :
    ¬ PosCorr consultations (fun c => c.1 == 0) (fun c => c.2 == 50) := by
  decide

/-! #### The content-level reading

A richer world with two possible questions and two possible hexagrams. Any
question causes the toss and the toss causes whichever hexagram falls. -/

inductive IQ | aboutBook | aboutWeather deriving DecidableEq
inductive IH | coinsTossed | caldron | creative deriving DecidableEq

def ichingTrialEdge : Sum IQ IH → Sum IQ IH → Bool
  | .inl _, .inr .coinsTossed => true
  | .inr .coinsTossed, .inr .caldron => true
  | .inr .coinsTossed, .inr .creative => true
  | _, _ => false

def ichingOutcome : Bool → IH
  | true => .caldron
  | false => .creative

def isBook : IQ → Bool
  | .aboutBook => true
  | .aboutWeather => false

def isCaldron : IH → Bool
  | .caldron => true
  | _ => false

/-- A trial is a question together with which hexagram fell. -/
@[reducible] def ichingTrialW : Model where
  U := IQ × Bool
  M := IQ
  P := IH
  A := Arch
  ψ := Prod.fst
  φ := fun u => ichingOutcome u.2
  causes := fun x y => ichingTrialEdge x y = true
  constellated := fun a u => a = Arch.wholeness ∧ u = (IQ.aboutBook, true)
  expressesM := fun a m => a = Arch.wholeness ∧ m = IQ.aboutBook
  expressesP := fun a p => a = Arch.wholeness ∧ p = IH.caldron

/-- The ensemble of trials (illustrative: every combination once). -/
def ichingTrials : List (IQ × Bool) :=
  [(.aboutBook, true), (.aboutBook, false), (.aboutWeather, true), (.aboutWeather, false)]

/-- The question causes the hexagram to occur. -/
theorem iching_trial_causal : Controls ichingTrialW IQ.aboutBook IH.caldron :=
  Path.tail (b := (Sum.inr IH.coinsTossed : Sum ichingTrialW.M ichingTrialW.P))
    (Path.single rfl) rfl

/-- Across trials, what is asked is independent of what falls. -/
theorem iching_trial_indep :
    Indep ichingTrials (fun u => isBook u.1) (fun u => isCaldron (ichingOutcome u.2)) := by
  decide

/-- **The I Ching case is a content synchronicity**: meaningful, occurring,
causally produced, and statistically unforced. -/
theorem iching_content_sync :
    ContentSynchronicity ichingTrialW ichingTrials isBook isCaldron (IQ.aboutBook, true) :=
  ⟨by decide,
   ⟨Arch.wholeness, (IQ.aboutBook, true), ⟨rfl, rfl⟩, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩,
   rfl, rfl, iching_trial_indep.not_posCorr⟩

/-- ...and not a strict one. Together with `strict_not_content`, the two
notions are logically independent. -/
theorem iching_content_not_strict :
    ¬ Synchronicity ichingTrialW IQ.aboutBook IH.caldron :=
  not_sync_of_linked ichingTrialW (Or.inl iching_trial_causal)

/-! ### 9. Rhine's card-guessing experiments (Duke, 1930s)

Jung leaned on J. B. Rhine's Zener-card tests: 25 cards, 5 symbols, chance
rate 1/5. Idealize perfect screening (no causal channel) and suppose a run
above chance. The frequency layer then refutes the statistical Reichenbach
principle. The empirical status of Rhine's results is disputed; the theorem is
conditional on the idealization. -/

def rhineGuesses : List Nat := [0, 0, 1, 3, 2, 4, 0, 1, 2, 3]
def rhineCards   : List Nat := [0, 0, 2, 4, 2, 1, 3, 1, 4, 0]

@[reducible] def rhineW : Model where
  U := Nat
  M := Nat
  P := Nat
  A := Arch
  ψ := fun i => rhineGuesses.getD i 0
  φ := fun i => rhineCards.getD i 0
  causes := fun _ _ => False
  constellated := fun a _ => a = Arch.psi
  expressesM := fun _ _ => True
  expressesP := fun _ _ => True

/-- "Guess star" and "card star" correlate (3·3 < 2·10). -/
theorem rhine_corr :
    PosCorr (List.range 10)
      (fun i => rhineGuesses.getD i 0 == 0) (fun i => rhineCards.getD i 0 == 0) := by
  decide

/-- 4 hits in 10 beat the chance rate 1/5. -/
theorem rhine_above_chance : AboveChance 4 10 1 5 := by decide

/-- The decline effect: a later run of 5 hits in 25 is exactly at chance. -/
theorem rhine_decline : ¬ AboveChance 5 25 1 5 := by decide

theorem rhine_refutes_stat_reichenbach :
    ¬ StatReichenbach rhineW (List.range 10) :=
  stat_reichenbach_fails_of_corr rhineW (fun _ _ h => h) (List.range 10)
    (fun g => g == 0) (fun c => c == 0) rhine_corr

/-- No cause, but a ground: conditional on the neutral state (the trial), the
guess and the card are independent. -/
theorem rhine_ground (i : Nat) :
    Indep ((List.range 10).filter (fun j => j == i))
      (fun j => rhineGuesses.getD j 0 == 0) (fun j => rhineCards.getD j 0 == 0) :=
  neutral_screens_off rhineW (List.range 10) (fun g => g == 0) (fun c => c == 0) i

/-- A subject who could *use* the effect would no longer exhibit it. -/
theorem rhine_exploited (g c : Nat) : ¬ Synchronicity (rhineW.exploit g c) g c :=
  exploit_destroys_sync rhineW g c

/-! ### 10. Jung's astrological marriage experiment (1952)

Jung tallied classical marriage aspects (sun–moon conjunctions and the like)
in the horoscopes of married couples, in successive batches. Each early batch
favoured a classical aspect, but the effect did not survive pooling, which
Jung read as a sign that synchronicity is sporadic and sensitive to the
experimenter's expectation. -/

/-- An early batch above a 1/20 chance rate (18 of 180)... -/
theorem astro_first_batch : AboveChance 18 180 1 20 := by decide

/-- ...while the pooled sample sits at chance (24 of 483). -/
theorem astro_pooled : ¬ AboveChance 24 483 1 20 := by decide

/-- Sporadic in the statistical sense: present in a part, absent in the whole. -/
theorem astro_sporadic : AboveChance 18 180 1 20 ∧ ¬ AboveChance 24 483 1 20 :=
  ⟨astro_first_batch, astro_pooled⟩

/-! ## Scorecard

| Case | Strict synchronicity? | Key theorem |
|---|---|---|
| Scarab | yes, even with a common observer | `scarab_sync`, `scarab_collider_sync` |
| Pauli effect | yes | `pauli_effect_sync` |
| Birds at the death | yes | `birds_sync` |
| Swedenborg's fire | yes | `swedenborg_sync` |
| Plum pudding | 2 of 3 episodes | `pudding_dinner_sync`, `pudding_boyhood_not_sync` |
| April fish | no, per encounter | `fish_not_sync_individually` |
| Room 137 | yes, not his physics | `lawlike_not_everywhere_sync` |
| I Ching | no; content-level yes | `iching_not_strict_sync`, `iching_content_sync` |
| Rhine | statistical | `rhine_refutes_stat_reichenbach`, `rhine_ground` |
| Astrology | statistical, sporadic | `astro_sporadic` |
-/

/-- The scorecard as a single machine-checked statement. -/
theorem scorecard :
    Synchronicity scarabW ScarabM.recountsDream ScarabP.beetleTaps ∧
    Synchronicity pauliW PauliM.pauliOnTrain PauliP.apparatusFails ∧
    Synchronicity birdsW BirdsM.wifeAlarmed BirdsP.husbandCollapses ∧
    Synchronicity swedW SwedM.visionOfFire SwedP.fireSpreads ∧
    (Synchronicity puddingW PuddingM.ordersPudding PuddingP.lastPuddingTaken ∧
      Synchronicity puddingW PuddingM.remarksAbsence PuddingP.fontgibuEnters ∧
      ¬ Synchronicity puddingW PuddingM.tastesPudding PuddingP.fontgibuGivesPudding) ∧
    (∀ u, ¬ Synchronicity fishW (fishW.ψ u) (fishW.φ u)) ∧
    (Synchronicity room137W R137M.preoccupiedWith137 R137P.assignedRoom137 ∧
      ¬ Synchronicity room137W R137M.computesAlpha R137P.spectrumMeasured) ∧
    (¬ Synchronicity ichingW IChingM.asksAboutBook IChingP.hexagram50 ∧
      ContentSynchronicity ichingTrialW ichingTrials isBook isCaldron (IQ.aboutBook, true)) ∧
    ¬ StatReichenbach rhineW (List.range 10) ∧
    (AboveChance 18 180 1 20 ∧ ¬ AboveChance 24 483 1 20) :=
  ⟨scarab_sync, pauli_effect_sync, birds_sync, swedenborg_sync,
   ⟨pudding_restaurant_sync, pudding_dinner_sync, pudding_boyhood_not_sync⟩,
   fish_not_sync_individually,
   ⟨room137_sync, alpha_work_not_sync⟩,
   ⟨iching_not_strict_sync, iching_content_sync⟩,
   rhine_refutes_stat_reichenbach, astro_sporadic⟩

end PauliJung
