function agda-unused $argv
  command agda-unused --root /data/code/prover/src
end

function echo-space $argv
  echo; echo $argv; echo
end

function with-dir
  set dir (pwd); cd $argv[1]
  eval $argv[2..-1]; set st $status
  cd $dir; return $st
end

function check-agda
  argparse --name=check-agda 'a/all' -- $argv

  if test $_flag_all
    echo-space 'Checking Agda code:'
  end

  set modules (agda-roots --root /data/code/prover/src); or return $status

  for module in $modules
    echo-space "Checking $module:"
    with-dir /data/code/prover/src agda \
      --local-interfaces \
      --no-libraries \
      --include-path=. \
      $module
    or return $status
  end

  agda-unused
end

function build-agda
  argparse --name=build-agda 'a/all' -- $argv

  if test $_flag_all
    check-agda --all; or return $status
    echo-space 'Building Agda code:'
  end

  with-dir /data/code/prover/src agda \
    --compile \
    --ghc-dont-call-ghc \
    --local-interfaces \
    --no-libraries \
    --include-path=. \
    Main.agda
end

function build-hs
  argparse --name=build-exe 'a/all' -- $argv

  if test $_flag_all
    build-agda --all; or return $status
    echo-space 'Building Haskell code:'
  end

  with-dir /data/code/prover cabal new-build prover
end

function run
  argparse --name=run 'a/all' -- $argv

  if test $_flag_all
    build-agda --all; or return $status
    echo-space 'Running Haskell executable:'
  end

  with-dir /data/code/prover cabal new-run
end

