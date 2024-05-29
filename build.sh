echo "Building language implementation..."

echo "Building interpreter..."
cd ./arc
source ./lib/make_trans_template.sh ./lib/transpile_template.ml
dune build
cd ..
if [ -e arc.exe ] 
then rm -f ./arc.exe
fi
mv -f ./arc/_build/default/src/arc.exe ./arc.exe

if [ -e arc_test.exe ] 
then rm -f ./arc_test.exe
fi
mv -f ./arc/_build/default/test/arc_test.exe ./arc_test.exe

echo "Done"
