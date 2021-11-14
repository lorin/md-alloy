/*
 A repository

  We use it to model git and debian repositories.


 */
one sig Repo {
  var commits: set Commit,
  var packages: set Deb
}

sig Commit {}

sig Deb {
  commit: Commit
}


/*
  Push a new commit to the repo
 */
pred push[c: Commit] {
  // c is not in the repo yet
  no c & Repo.commits
  commits' = commits + Repo->c
  packages' = packages
}

/*
 Build a commit into a deb
*/
pred build[c : Commit, d: Deb] {
  some c & Repo.commits // commit is in the repository
  d.commit = c // commit is associated with the deb
  packages' = packages + Repo->d  // deb gets added
  commits' = commits

}

pred stutter {
  commits' = commits
  packages' = packages
}

fact debsHaveUniqueCommits {
  all disj d1, d2 : Deb | no d1.commit & d2.commit

}

fact transitions {
  always (
    stutter or
    (some c : Commit | push[c]) or
    (some c: Commit, d: Deb | build[c, d])
  )
}

/*
  Build action is enabled when the commit is in the repository
*/
pred buildEnabled[c: Commit] {
  some c & Repo.commits
}

pred buildWeakFairness { all c : Commit |
  (eventually always buildEnabled[c]) implies
  (always eventually some d: Deb | build[c, d])

}


// run {}

assert everyPushedCommitWillBeBuilt {
    //buildWeakFairness implies
    all c : Commit | always (push[c] implies eventually some d: Repo.packages | d.commit = c)

}

check everyPushedCommitWillBeBuilt
