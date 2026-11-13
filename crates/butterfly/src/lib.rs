//! Typed finite-model search. Search is an untrusted witness producer; only a
//! separate checker can turn a witness into a rejected conservation claim.
use scribe_core::{
    Claim, Corpus, Diagnostics, Discrimination, Evidence, Instance, Oracle, Outcome, Reason,
    Verdict,
};
use serde::{Deserialize, Serialize};
use std::{
    collections::{HashMap, VecDeque},
    fs,
    path::PathBuf,
    process::{Command, Stdio},
    sync::atomic::{AtomicU64, Ordering},
    time::{Duration, Instant},
};

pub const CAP: u32 = 8;
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct State {
    pub reserve: u32,
    pub alice: u32,
    pub bob: u32,
    pub treasury: u32,
}
pub const INITIAL: State = State {
    reserve: 8,
    alice: 0,
    bob: 0,
    treasury: 0,
};
impl State {
    pub fn total(self) -> u32 {
        self.reserve + self.alice + self.bob + self.treasury
    }
    fn bounded(self) -> bool {
        [self.reserve, self.alice, self.bob, self.treasury]
            .iter()
            .all(|x| *x <= CAP)
    }
    fn balance(self, a: Account) -> u32 {
        match a {
            Account::Alice => self.alice,
            Account::Bob => self.bob,
        }
    }
    fn set(&mut self, a: Account, n: u32) {
        match a {
            Account::Alice => self.alice = n,
            Account::Bob => self.bob = n,
        }
    }
    fn lean(self) -> String {
        format!(
            "{{ reserve := {}, alice := {}, bob := {}, treasury := {} }}",
            self.reserve, self.alice, self.bob, self.treasury
        )
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Account {
    Alice,
    Bob,
}
impl Account {
    fn other(self) -> Self {
        match self {
            Self::Alice => Self::Bob,
            Self::Bob => Self::Alice,
        }
    }
    fn lean(self) -> &'static str {
        match self {
            Self::Alice => ".alice",
            Self::Bob => ".bob",
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum Action {
    Issue { account: Account, amount: u32 },
    Trade { account: Account, amount: u32 },
}
impl Action {
    fn lean(self) -> String {
        match self {
            Self::Issue { account, amount } => format!("(.issue {} {})", account.lean(), amount),
            Self::Trade { account, amount } => format!("(.trade {} {})", account.lean(), amount),
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Mutation {
    Baseline,
    BoundaryRelax,
    GuardRemoved,
    WrongDebit,
    DuplicateCredit,
    BoundaryStrict,
    UnreachableBonus,
}
impl Mutation {
    pub const ALL: [Self; 7] = [
        Self::Baseline,
        Self::BoundaryRelax,
        Self::GuardRemoved,
        Self::WrongDebit,
        Self::DuplicateCredit,
        Self::BoundaryStrict,
        Self::UnreachableBonus,
    ];
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Baseline => "baseline",
            Self::BoundaryRelax => "boundary_relax",
            Self::GuardRemoved => "guard_removed",
            Self::WrongDebit => "wrong_debit",
            Self::DuplicateCredit => "duplicate_credit",
            Self::BoundaryStrict => "boundary_strict",
            Self::UnreachableBonus => "unreachable_bonus",
        }
    }
    fn lean(self) -> &'static str {
        match self {
            Self::Baseline => ".baseline",
            Self::BoundaryRelax => ".boundaryRelax",
            Self::GuardRemoved => ".guardRemoved",
            Self::WrongDebit => ".wrongDebit",
            Self::DuplicateCredit => ".duplicateCredit",
            Self::BoundaryStrict => ".boundaryStrict",
            Self::UnreachableBonus => ".unreachableBonus",
        }
    }
    pub fn description(self) -> &'static str {
        match self {Self::Baseline=>"Original trade: amount < balance; debit amount + 1; credit amount; treasury + 1",Self::BoundaryRelax=>"Trade guard: amount < balance → amount ≤ balance",Self::GuardRemoved=>"Trade guard: amount < balance → true",Self::WrongDebit=>"Trade debit: amount + 1 → amount",Self::DuplicateCredit=>"Recipient credit: amount → 2 × amount",Self::BoundaryStrict=>"Trade guard: amount < balance → amount + 1 < balance",Self::UnreachableBonus=>"Recipient credit: amount → if amount > 8 then 2 × amount else amount (unreachable branch)"}
    }
    pub fn expected(self) -> Expected {
        match self {
            Self::Baseline | Self::BoundaryStrict => Expected::Safe,
            Self::UnreachableBonus => Expected::UnreachableFault,
            _ => Expected::Harmful,
        }
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Expected {
    Harmful,
    Safe,
    UnreachableFault,
}
/// Rust search semantics mirror Lean; a match is not itself proof of correctness.
pub fn step(variant: Mutation, s: State, action: Action) -> Option<State> {
    if !s.bounded() {
        return None;
    }
    let (account, amount) = match action {
        Action::Issue { account, amount } | Action::Trade { account, amount } => (account, amount),
    };
    if !(1..=CAP).contains(&amount) {
        return None;
    }
    let mut out = s;
    match action {
        Action::Issue { .. } => {
            if amount > s.reserve {
                return None;
            };
            out.reserve -= amount;
            out.set(account, s.balance(account) + amount);
        }
        Action::Trade { .. } => {
            let balance = s.balance(account);
            let guard = match variant {
                Mutation::BoundaryRelax => amount <= balance,
                Mutation::GuardRemoved => true,
                Mutation::BoundaryStrict => amount + 1 < balance,
                _ => amount < balance,
            };
            if !guard {
                return None;
            }
            let debit = if variant == Mutation::WrongDebit {
                amount
            } else {
                amount + 1
            };
            let credit = if variant == Mutation::DuplicateCredit
                || (variant == Mutation::UnreachableBonus && amount > CAP)
            {
                2 * amount
            } else {
                amount
            };
            out.set(account, balance.saturating_sub(debit));
            out.set(account.other(), s.balance(account.other()) + credit);
            out.treasury += 1;
        }
    }
    out.bounded().then_some(out)
}
fn actions() -> impl Iterator<Item = Action> {
    [Account::Alice, Account::Bob]
        .into_iter()
        .flat_map(|account| {
            (1..=CAP).flat_map(move |amount| {
                [
                    Action::Issue { account, amount },
                    Action::Trade { account, amount },
                ]
            })
        })
}
#[derive(Debug, Clone, Copy, Serialize)]
pub struct SearchBudget {
    pub max_depth: usize,
    pub max_nodes: usize,
    pub max_edges: usize,
    pub max_duration: Duration,
}
impl Default for SearchBudget {
    fn default() -> Self {
        Self {
            max_depth: 6,
            max_nodes: 20_000,
            max_edges: 500_000,
            max_duration: Duration::from_secs(10),
        }
    }
}
#[derive(Debug, Clone, Serialize)]
pub struct SearchStats {
    pub nodes: usize,
    pub edges: usize,
    pub max_depth: usize,
    pub elapsed_ms: u128,
}
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CandidateWitness {
    pub variant: Mutation,
    pub actions: Vec<Action>,
    pub states: Vec<State>,
    pub baseline_divergence: usize,
}
#[derive(Debug, Clone, Serialize)]
pub struct SearchResult {
    pub candidate: Option<CandidateWitness>,
    pub stats: SearchStats,
    pub termination: String,
}
/// FIFO search finds a shortest trace in this finite action alphabet when it
/// reaches a violation. This algorithmic observation is NOT kernel-certified.
pub fn search(variant: Mutation, budget: SearchBudget) -> SearchResult {
    let start = Instant::now();
    let mut stats = SearchStats {
        nodes: 1,
        edges: 0,
        max_depth: 0,
        elapsed_ms: 0,
    };
    let mut queue = VecDeque::from([(INITIAL, 0usize)]);
    let mut parent = HashMap::<State, (State, Action)>::new();
    parent.insert(
        INITIAL,
        (
            INITIAL,
            Action::Issue {
                account: Account::Alice,
                amount: 1,
            },
        ),
    );
    let mut termination = "finite_frontier_exhausted";
    let mut found = None;
    let mut depth_limited = false;
    if budget.max_nodes == 0 {
        termination = "node_budget";
        queue.clear();
        stats.nodes = 0;
    }
    'bfs: while let Some((state, depth)) = queue.pop_front() {
        if depth >= budget.max_depth {
            depth_limited = true;
            continue;
        }
        for action in actions() {
            if start.elapsed() >= budget.max_duration {
                termination = "time_budget";
                break 'bfs;
            }
            if stats.edges >= budget.max_edges {
                termination = "edge_budget";
                break 'bfs;
            }
            stats.edges += 1;
            let Some(next) = step(variant, state, action) else {
                continue;
            };
            if parent.contains_key(&next) {
                continue;
            }
            if stats.nodes >= budget.max_nodes {
                termination = "node_budget";
                break 'bfs;
            }
            parent.insert(next, (state, action));
            stats.nodes += 1;
            stats.max_depth = stats.max_depth.max(depth + 1);
            if next.total() != INITIAL.total() {
                let mut states = vec![next];
                let mut acts = vec![];
                let mut cursor = next;
                while cursor != INITIAL {
                    let (previous, a) = parent[&cursor];
                    acts.push(a);
                    states.push(previous);
                    cursor = previous;
                }
                acts.reverse();
                states.reverse();
                let divergence = acts
                    .iter()
                    .enumerate()
                    .find(|(i, a)| {
                        step(Mutation::Baseline, states[*i], **a) != Some(states[*i + 1])
                    })
                    .map(|(i, _)| i)
                    .expect("baseline conserves resources");
                found = Some(CandidateWitness {
                    variant,
                    actions: acts,
                    states,
                    baseline_divergence: divergence,
                });
                termination = "candidate_found";
                break 'bfs;
            }
            queue.push_back((next, depth + 1));
        }
    }
    if found.is_none() && termination == "finite_frontier_exhausted" && depth_limited {
        termination = "depth_budget"
    }
    stats.elapsed_ms = start.elapsed().as_millis();
    SearchResult {
        candidate: found,
        stats,
        termination: termination.into(),
    }
}

#[derive(Debug)]
pub enum CheckResult {
    Verified(Evidence),
    Invalid(String),
    Unavailable(String),
}
pub trait WitnessChecker {
    fn check(&self, candidate: &CandidateWitness) -> CheckResult;
    fn check_safety(&self, _variant: Mutation) -> CheckResult {
        CheckResult::Unavailable("No independent safety proof checker configured".into())
    }
}
/// Only typed finite values enter generated Lean. This is a trusted-source
/// checker, NOT a sandbox for model-generated Lean or an untrusted Lake project.
pub struct LeanChecker {
    lake_dir: PathBuf,
    output_dir: PathBuf,
    timeout: Duration,
}
impl LeanChecker {
    pub fn new(lake_dir: PathBuf, output_dir: PathBuf, timeout: Duration) -> Self {
        Self {
            lake_dir,
            output_dir,
            timeout,
        }
    }
}
fn validate_candidate(c: &CandidateWitness) -> Result<(), String> {
    if c.actions.is_empty()
        || c.actions.len() > 1000
        || c.states.len() != c.actions.len() + 1
        || c.states.first() != Some(&INITIAL)
    {
        return Err("invalid trace shape or initial state".into());
    }
    if c.states.iter().any(|s| !s.bounded()) {
        return Err("state outside finite domain".into());
    }
    for (i, a) in c.actions.iter().enumerate() {
        if step(c.variant, c.states[i], *a) != Some(c.states[i + 1]) {
            return Err(format!("invalid transition {i}"));
        }
    }
    let first = c
        .actions
        .iter()
        .enumerate()
        .find(|(i, a)| step(Mutation::Baseline, c.states[*i], **a) != Some(c.states[*i + 1]))
        .map(|(i, _)| i);
    if first != Some(c.baseline_divergence) {
        return Err("incorrect first baseline divergence".into());
    }
    if c.states.last().unwrap().total() == INITIAL.total() {
        return Err("trace does not violate conservation".into());
    }
    Ok(())
}
/// Frozen source checks every intermediate state and the first divergence.
pub fn certificate_source(c: &CandidateWitness) -> Result<String, String> {
    validate_candidate(c)?;
    let mut propositions = vec![format!("({} : State) = initial", c.states[0].lean())];
    for (i, a) in c.actions.iter().enumerate() {
        propositions.push(format!(
            "step {} {} {} = some {}",
            c.variant.lean(),
            c.states[i].lean(),
            a.lean(),
            c.states[i + 1].lean()
        ));
        if i <= c.baseline_divergence {
            propositions.push(format!(
                "step .baseline {} {} {} some {}",
                c.states[i].lean(),
                a.lean(),
                if i == c.baseline_divergence {
                    "≠"
                } else {
                    "="
                },
                c.states[i + 1].lean()
            ));
        }
    }
    propositions.push(format!(
        "total {} ≠ total initial",
        c.states.last().unwrap().lean()
    ));
    Ok(format!("import ZkGadgets.Butterfly.Model\nimport ZkGadgets.Audit\nopen Butterfly\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\ntheorem butterflyWitness :\n  {} := by decide\n#audit_axioms butterflyWitness\n#eval IO.println \"BUTTERFLY_CHECKED_WITNESS_V1\"\n",propositions.join(" ∧\n  ")))
}
static NEXT: AtomicU64 = AtomicU64::new(0);
fn run_bounded(
    mut command: Command,
    dir: &std::path::Path,
    label: &str,
    deadline: Instant,
) -> Result<String, String> {
    let out_path = dir.join(format!("{label}-stdout.log"));
    let err_path = dir.join(format!("{label}-stderr.log"));
    command
        .stdin(Stdio::null())
        .stdout(fs::File::create(&out_path).map_err(|e| e.to_string())?)
        .stderr(fs::File::create(&err_path).map_err(|e| e.to_string())?);
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        command.process_group(0);
    }
    if Instant::now() >= deadline {
        return Err("Lean deadline exhausted before launch".into());
    }
    let mut child = command
        .spawn()
        .map_err(|e| format!("cannot start Lean: {e}"))?;
    let terminate = |child: &mut std::process::Child| {
        #[cfg(unix)]
        {
            let _ = Command::new("kill")
                .args(["-KILL", "--", &format!("-{}", child.id())])
                .status();
        }
        let _ = child.kill();
        let _ = child.wait();
    };
    let status = loop {
        let output_size = fs::metadata(&out_path).map(|m| m.len()).unwrap_or(0)
            + fs::metadata(&err_path).map(|m| m.len()).unwrap_or(0);
        if Instant::now() >= deadline || output_size > 4 * 1024 * 1024 {
            terminate(&mut child);
            return Err(format!(
                "Lean timeout or output budget exhausted; evidence {}",
                dir.display()
            ));
        }
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) => {}
            Err(e) => {
                terminate(&mut child);
                return Err(e.to_string());
            }
        }
        std::thread::sleep(Duration::from_millis(20));
    };
    let final_output_size = fs::metadata(&out_path).map(|m| m.len()).unwrap_or(0)
        + fs::metadata(&err_path).map(|m| m.len()).unwrap_or(0);
    if Instant::now() >= deadline || final_output_size > 4 * 1024 * 1024 {
        return Err("Lean completed outside time/output budget".into());
    }
    if !status.success() {
        return Err(format!(
            "Lean {label} failed ({status}); evidence {}",
            dir.display()
        ));
    }
    let stdout = fs::read_to_string(&out_path).map_err(|e| e.to_string())?;
    Ok(stdout)
}
impl LeanChecker {
    fn verify_source(&self, variant: Mutation, source: String, summary: &str) -> CheckResult {
        let run = || -> Result<Evidence, String> {
            use sha2::{Digest, Sha256};
            let start = Instant::now();
            let deadline = start.checked_add(self.timeout).ok_or("invalid timeout")?;
            fs::create_dir_all(&self.output_dir).map_err(|e| e.to_string())?;
            let dir = loop {
                let dir = self.output_dir.join(format!(
                    "{}-{}-{}",
                    variant.as_str(),
                    std::process::id(),
                    NEXT.fetch_add(1, Ordering::Relaxed)
                ));
                match fs::create_dir(&dir) {
                    Ok(()) => break fs::canonicalize(dir).map_err(|e| e.to_string())?,
                    Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(e) => return Err(e.to_string()),
                }
            };
            let source_path = dir.join("Witness.lean");
            fs::write(&source_path, &source).map_err(|e| e.to_string())?;
            let mut hashes = std::collections::BTreeMap::new();
            for (relative, snapshot) in [
                ("ZkGadgets/Butterfly/Model.lean", "Model.lean"),
                ("ZkGadgets/Audit.lean", "Audit.lean"),
                ("lean-toolchain", "lean-toolchain"),
                ("lakefile.toml", "lakefile.toml"),
                ("lake-manifest.json", "lake-manifest.json"),
            ] {
                let bytes = fs::read(self.lake_dir.join(relative)).map_err(|e| e.to_string())?;
                hashes.insert(
                    relative.to_string(),
                    format!("{:x}", Sha256::digest(&bytes)),
                );
                fs::write(dir.join(snapshot), bytes).map_err(|e| e.to_string())?;
            }
            hashes.insert(
                "Witness.lean".into(),
                format!("{:x}", Sha256::digest(source.as_bytes())),
            );
            fs::write(
                dir.join("sha256.json"),
                serde_json::to_vec_pretty(&hashes).unwrap(),
            )
            .map_err(|e| e.to_string())?;
            let mut build = Command::new("lake");
            build
                .args(["build", "ZkGadgets.Butterfly.Model", "ZkGadgets.Audit"])
                .current_dir(&self.lake_dir);
            run_bounded(build, &dir, "build", deadline)?;
            let mut check = Command::new("lake");
            check
                .args(["env", "lean"])
                .arg(&source_path)
                .current_dir(&self.lake_dir);
            let stdout = run_bounded(check, &dir, "check", deadline)?;
            if !stdout.lines().any(|l| l == "BUTTERFLY_CHECKED_WITNESS_V1") {
                return Err(format!(
                    "Lean acceptance receipt missing; evidence {}",
                    dir.display()
                ));
            }
            // Do not bind evidence to a different source revision during a concurrent edit.
            for (relative, hash) in &hashes {
                if relative != "Witness.lean" {
                    let bytes =
                        fs::read(self.lake_dir.join(relative)).map_err(|e| e.to_string())?;
                    if format!("{:x}", Sha256::digest(bytes)) != *hash {
                        return Err("Trusted Lean sources changed during checking".into());
                    }
                }
            }
            if Instant::now() >= deadline {
                return Err("Lean completed after deadline".into());
            }
            Ok(Evidence{summary:summary.into(),details:vec![format!("certificate: {}",source_path.display()),format!("evidence directory: {}",dir.display()),format!("verifier elapsed ms: {}",start.elapsed().as_millis()),format!("source SHA-256 manifest: {}",dir.join("sha256.json").display()),"Trusted local Lean/Lake project and fixed emitter; no native_decide or custom axioms".into(),"Shortest-trace search observation is not part of the checked theorem".into()]})
        };
        match run() {
            Ok(e) => CheckResult::Verified(e),
            Err(e) => CheckResult::Unavailable(e),
        }
    }
}
impl WitnessChecker for LeanChecker {
    fn check(&self, c: &CandidateWitness) -> CheckResult {
        let source = match certificate_source(c) {
            Ok(s) => s,
            Err(e) => return CheckResult::Invalid(e),
        };
        self.verify_source(c.variant,source,"Lean checked every mutant transition, conservation violation, and first baseline divergence")
    }
    fn check_safety(&self, variant: Mutation) -> CheckResult {
        let theorem = match variant {
            Mutation::Baseline => "baseline_conservation",
            Mutation::BoundaryStrict => "boundaryStrict_conservation",
            Mutation::UnreachableBonus => "unreachableBonus_conservation",
            _ => {
                return CheckResult::Unavailable(
                    "No independent safety theorem for this variant".into(),
                )
            }
        };
        let source=format!("import ZkGadgets.Butterfly.Model\nimport ZkGadgets.Audit\nopen Butterfly\ntheorem butterflySafety (actions : List Action) (t : State) : execute {} actions = some t → total t = 8 := {}\n#audit_axioms butterflySafety\n#eval IO.println \"BUTTERFLY_CHECKED_WITNESS_V1\"\n",variant.lean(),theorem);
        self.verify_source(variant,source,"Lean checked universal conservation using a separate safety theorem, not search absence")
    }
}
#[derive(Clone, Copy)]
pub struct ConservationClaim;
impl Claim for ConservationClaim {
    type Subject = Mutation;
    fn kind(&self) -> &'static str {
        "resource-conservation"
    }
    fn describe(&self) -> String {
        "Every reachable trade state conserves total issued resources".into()
    }
}
pub struct MutationCorpus;
impl Corpus<ConservationClaim> for MutationCorpus {
    fn negatives(&self) -> Vec<Instance<ConservationClaim>> {
        instances(true)
    }
    fn positives(&self) -> Vec<Instance<ConservationClaim>> {
        instances(false)
    }
    fn version(&self) -> &str {
        "butterfly-trading-v1"
    }
}
fn instances(harmful: bool) -> Vec<Instance<ConservationClaim>> {
    Mutation::ALL
        .into_iter()
        .filter(|v| (v.expected() == Expected::Harmful) == harmful)
        .map(|v| Instance {
            id: v.as_str().into(),
            claim: ConservationClaim,
            subject: v,
        })
        .collect()
}
fn adjudicate_result(
    checker: &impl WitnessChecker,
    variant: Mutation,
    result: &SearchResult,
) -> (Outcome, &'static str) {
    // The fixed theorem registry is independent of corpus labels. No theorem
    // for a variant means ordinary bounded inconclusiveness, not tool failure.
    if result.candidate.is_none()
        && !matches!(
            variant,
            Mutation::Baseline | Mutation::BoundaryStrict | Mutation::UnreachableBonus
        )
    {
        return (
            Outcome::Undetermined(Reason {
                summary: format!(
                    "No exploit found: {}; no independent safety theorem configured",
                    result.termination
                ),
            }),
            "not_attempted",
        );
    }
    let checked = match &result.candidate {
        Some(c) => checker.check(c),
        None => checker.check_safety(variant),
    };
    match checked {
        CheckResult::Verified(e) if result.candidate.is_some() => (
            Outcome::Reject(Diagnostics {
                summary: e.summary,
                details: e.details,
            }),
            "checked_refutation",
        ),
        CheckResult::Verified(e) => (Outcome::Accept(e), "checked_safe"),
        CheckResult::Invalid(e) => (Outcome::Undetermined(Reason { summary: e }), "rejected"),
        CheckResult::Unavailable(e) => (
            Outcome::Undetermined(Reason {
                summary: format!(
                    "{e}; search termination: {}. Search absence does not prove safety.",
                    result.termination
                ),
            }),
            "unavailable",
        ),
    }
}
pub struct ConservationOracle<C> {
    pub checker: C,
    pub budget: SearchBudget,
}
impl<C: WitnessChecker> Oracle<ConservationClaim> for ConservationOracle<C> {
    fn adjudicate(&self, _: &ConservationClaim, subject: &Mutation) -> Outcome {
        adjudicate_result(&self.checker, *subject, &search(*subject, self.budget)).0
    }
}
#[derive(Serialize)]
pub struct CaseReport {
    pub variant: Mutation,
    pub expected: Expected,
    pub original_rule: &'static str,
    pub mutant_rule: &'static str,
    pub search: SearchResult,
    pub verification_status: &'static str,
    pub verifier_elapsed_ms: u128,
    pub verdict: Verdict,
}
#[derive(Serialize)]
pub struct EvaluationReport {
    pub schema_version: u32,
    pub corpus_version: &'static str,
    pub budget: SearchBudget,
    pub cases: Vec<CaseReport>,
    pub checked_witnesses: usize,
    pub harmful_total: usize,
    pub safe_false_accusations: usize,
    pub safe_total: usize,
    pub limitations: Vec<&'static str>,
}
/// Corpus labels measure results after checking; they never decide an outcome.
pub fn evaluate(checker: &impl WitnessChecker, budget: SearchBudget) -> EvaluationReport {
    let raw: Vec<_> = Mutation::ALL
        .into_iter()
        .map(|variant| {
            let search = search(variant, budget);
            let start = Instant::now();
            let (outcome, status) = adjudicate_result(checker, variant, &search);
            (
                variant,
                search,
                outcome,
                status,
                start.elapsed().as_millis(),
            )
        })
        .collect();
    struct Cached<'a>(&'a [(Mutation, SearchResult, Outcome, &'static str, u128)]);
    impl Oracle<ConservationClaim> for Cached<'_> {
        fn adjudicate(&self, _: &ConservationClaim, s: &Mutation) -> Outcome {
            self.0
                .iter()
                .find(|(v, _, _, _, _)| v == s)
                .unwrap()
                .2
                .clone()
        }
    }
    let measurement = scribe_core::validate(&Cached(&raw), &MutationCorpus);
    let checked_witnesses = raw
        .iter()
        .filter(|(_, _, o, _, _)| matches!(o, Outcome::Reject(_)))
        .count();
    let safe_false_accusations = raw
        .iter()
        .filter(|(v, _, o, _, _)| {
            v.expected() != Expected::Harmful && matches!(o, Outcome::Reject(_))
        })
        .count();
    let cases = raw
        .into_iter()
        .map(
            |(variant, search, outcome, verification_status, verifier_elapsed_ms)| CaseReport {
                variant,
                expected: variant.expected(),
                original_rule: Mutation::Baseline.description(),
                mutant_rule: variant.description(),
                search,
                verification_status,
                verifier_elapsed_ms,
                verdict: Verdict::new(outcome, Discrimination::Measured(measurement.clone())),
            },
        )
        .collect();
    EvaluationReport{schema_version:1,corpus_version:"butterfly-trading-v1",budget,cases,checked_witnesses,harmful_total:4,safe_false_accusations,safe_total:3,limitations:vec!["Toy finite model: balances capped at 8, actions restricted to issue/trade amounts 1..8; not evidence about deployed protocols","Search absence never proves safety; Accept requires a separate independently checked universal safety theorem","BFS shortest witness is relative to this initial state and action alphabet and is not kernel-certified","Only trusted fixed Lean templates run; local Lean toolchain, imports, emitter, and audit are in the trust boundary"]}
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn harmful_variants_have_valid_traces_and_safe_controls_do_not() {
        for variant in Mutation::ALL {
            let result = search(variant, SearchBudget::default());
            if variant.expected() == Expected::Harmful {
                let c = result
                    .candidate
                    .expect("planted mutation must be reachable");
                validate_candidate(&c).unwrap();
                assert!(c.states.last().unwrap().total() > 8);
                assert!(certificate_source(&c)
                    .unwrap()
                    .contains("#audit_axioms butterflyWitness"));
            } else {
                assert!(result.candidate.is_none(), "{variant:?}")
            }
        }
    }
    #[test]
    fn boundary_change_needs_issuance_then_trade() {
        let c = search(Mutation::BoundaryRelax, SearchBudget::default())
            .candidate
            .unwrap();
        assert_eq!(
            c.actions,
            vec![
                Action::Issue {
                    account: Account::Alice,
                    amount: 1
                },
                Action::Trade {
                    account: Account::Alice,
                    amount: 1
                }
            ]
        );
        assert_eq!(c.baseline_divergence, 1);
        assert_eq!(c.states.last().unwrap().total(), 9);
        assert!(search(
            Mutation::BoundaryRelax,
            SearchBudget {
                max_depth: 1,
                ..Default::default()
            }
        )
        .candidate
        .is_none());
    }
    #[test]
    fn budgets_are_reported_and_never_prove_safety() {
        for (budget, expected) in [
            (
                SearchBudget {
                    max_nodes: 0,
                    ..Default::default()
                },
                "node_budget",
            ),
            (
                SearchBudget {
                    max_edges: 0,
                    ..Default::default()
                },
                "edge_budget",
            ),
            (
                SearchBudget {
                    max_depth: 0,
                    ..Default::default()
                },
                "depth_budget",
            ),
            (
                SearchBudget {
                    max_duration: Duration::ZERO,
                    ..Default::default()
                },
                "time_budget",
            ),
        ] {
            let result = search(Mutation::BoundaryRelax, budget);
            assert_eq!(result.termination, expected);
            assert!(result.candidate.is_none());
        }
    }
    #[test]
    fn witness_tampering_is_rejected_before_emission() {
        let c = search(Mutation::BoundaryRelax, SearchBudget::default())
            .candidate
            .unwrap();
        let mut bad = c.clone();
        bad.states[1].alice = 3;
        assert!(certificate_source(&bad).is_err());
        let mut bad = c.clone();
        bad.variant = Mutation::Baseline;
        assert!(certificate_source(&bad).is_err());
        let mut bad = c.clone();
        bad.baseline_divergence = 0;
        assert!(certificate_source(&bad).is_err());
        let mut bad = c.clone();
        bad.actions[1] = Action::Trade {
            account: Account::Bob,
            amount: 1,
        };
        assert!(certificate_source(&bad).is_err());
        let mut bad = c;
        bad.states[0].reserve = 9;
        assert!(certificate_source(&bad).is_err());
    }
    struct Unavailable;
    impl WitnessChecker for Unavailable {
        fn check(&self, _: &CandidateWitness) -> CheckResult {
            CheckResult::Unavailable("test unavailable".into())
        }
    }
    #[test]
    fn candidate_is_not_a_checked_refutation() {
        let report = evaluate(&Unavailable, SearchBudget::default());
        assert_eq!(report.checked_witnesses, 0);
        assert_eq!(report.safe_false_accusations, 0);
        assert!(report
            .cases
            .iter()
            .all(|c| matches!(c.verdict.outcome(), Outcome::Undetermined(_))));
    }
    #[test]
    fn certificate_binds_all_steps_and_baseline_first_divergence() {
        let c = search(Mutation::BoundaryRelax, SearchBudget::default())
            .candidate
            .unwrap();
        let source = certificate_source(&c).unwrap();
        assert_eq!(source.matches("step .boundaryRelax").count(), 2);
        assert_eq!(source.matches("step .baseline").count(), 2);
        assert!(source.contains("≠ some"));
        assert!(!source.contains("native_decide"));
    }
    #[test]
    fn depth_exhaustion_is_unknown_not_infrastructure_failure() {
        let report = evaluate(
            &Unavailable,
            SearchBudget {
                max_depth: 0,
                ..Default::default()
            },
        );
        for case in report
            .cases
            .iter()
            .filter(|c| c.expected == Expected::Harmful)
        {
            assert_eq!(case.verification_status, "not_attempted");
            assert!(matches!(case.verdict.outcome(), Outcome::Undetermined(_)));
        }
    }
    #[cfg(unix)]
    #[test]
    fn runner_kills_process_group_at_deadline() {
        let dir = std::env::temp_dir().join(format!(
            "butterfly-timeout-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&dir).unwrap();
        let mut command = Command::new("sh");
        command.args(["-c", "sleep 10"]);
        let start = Instant::now();
        let result = run_bounded(command, &dir, "timeout", start + Duration::from_millis(50));
        assert!(result.unwrap_err().contains("timeout"));
        assert!(start.elapsed() < Duration::from_secs(2));
        fs::remove_dir_all(dir).unwrap();
    }
}
