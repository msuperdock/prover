function echo-space $argv
  echo; echo $argv; echo
end

function with-dir
  set dir (pwd); cd $argv[1]
  eval $argv[2..-1]; set st $status
  cd $dir; return $st
end

function build-agda
  argparse --name=build-agda 'a/all' -- $argv

  if test $argv[1]
    set file $argv[1]
    set main '--no-main'
  else
    set file 'Main.agda'
    set main ''
  end

  if test $_flag_all
    echo-space 'Building agda code:'
  end

  with-dir /data/code/prover/src agda \
    --compile \
    --ghc-dont-call-ghc \
    --include-path=. \
    --no-libraries \
    $main \
    $file
end

function build-exe
  argparse --name=build-exe 'a/all' -- $argv

  if test $_flag_all
    build-agda --all; or return $status
    echo-space 'Building executable:'
  end

  with-dir /data/code/prover cabal new-build prover
end

function run
  argparse --name=run 'a/all' -- $argv

  if test $_flag_all
    build-agda --all; or return $status
    echo-space 'Running haskell executable:'
  end

  with-dir /data/code/prover cabal new-run
end
