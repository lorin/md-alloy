/**
 * git and debian repositories
 */
one sig Repo {
  var commits: set Commit,
  var packages: set Deb,
  var amis: set AMI
}

/**
 * Database tracks the latest debian built
 */
one sig DB {
  var latest: lone Deb
}

sig Commit {}

sig Deb {
  commit: Commit
}

sig AMI {
  deb: Deb
}


/**
 * Push a new commit to the repo
 */
pred push[c: Commit] {

  no c & Repo.commits   // c is not in the repo yet

  commits' = commits + Repo->c
  packages' = packages
  amis' = amis
  latest' = latest
}

/**
 * Build a commit into a deb
 */
pred build[c : Commit, d: Deb] {
  no d & Repo.packages
  some c & Repo.commits // commit is in the repository
  d.commit = c // commit is associated with the deb
  packages' = packages + Repo->d  // deb gets added
  latest' = DB->d // db marked as latest
  amis' = amis
  commits' = commits
}

/**
 * Bake the latest deb into an AMI
 */
 pred bake[d: Deb, a: AMI] {
   a.deb = d
   no d & Repo.amis.deb // d hasn't already been baked into an AMI yet
   d in DB.latest  // d is the latest
   d in Repo.packages // d is in the repository

   amis' = amis + Repo->a  // AMI gets added to the repo

   packages' = packages
   latest' = latest
   commits' = commits

 }

pred stutter {
  commits' = commits
  packages' = packages
  amis' = amis
  latest' = latest
}

fact debsHaveUniqueCommits {
  all disj d1, d2 : Deb | no d1.commit & d2.commit
}

fact amisHaveUniqueDebs {
  all disj a1, a2 : AMI | no a1.deb & a2.deb

}

fact init {
  no Repo.commits
  no Repo.packages
  no Repo.amis
  no DB.latest
}

fact transitions {
  always (
    stutter or
    (some c : Commit | push[c]) or
    (some c: Commit, d: Deb | build[c, d]) or
    (some d: Deb, a: AMI | bake[d, a])
  )
}

/**
 *  Build action is enabled when the commit is in the repository
 */
pred buildEnabled[c: Commit] {
  no commit.c & Repo.packages
  some c & Repo.commits
}

pred buildWeakFairness { all c : Commit |
  (eventually always buildEnabled[c]) implies
  (always eventually some d: Deb | build[c, d])
}


pred bakeEnabled[d: Deb] {
   no d & Repo.amis.deb // d hasn't already been baked into an AMI yet
   d in DB.latest  // d is the latest
   d in Repo.packages // d is in the repository
}

pred bakeWeakFairness { all d : Deb |
  (eventually always bakeEnabled[d]) implies
  (always eventually some a: AMI | bake[d, a])
}

pred liveness {
  buildWeakFairness
  bakeWeakFairness
}

pred behavior {
  liveness
}

assert everyPushedCommitWillBeBuilt {
    buildWeakFairness implies
    all c : Commit | always (push[c] implies eventually some d: Repo.packages | d.commit = c)

}

assert everyPushedCommitWillBeBaked {
  liveness implies all c : Commit | always (
    push[c] implies eventually some a: Repo.amis | a.deb.commit = c
  )
}

check everyPushedCommitWillBeBaked

run {
  buildWeakFairness

  some c1, c2 : Commit | no c1 & c2
  all c : Commit | eventually push[c]
}

