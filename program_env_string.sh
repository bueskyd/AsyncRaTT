
PROG_ENV=$1
TARGET=$2

function file_content {
  cat $1 | sed 's/%/%%/g' | sed 's/\\/\\\\/g' | sed 's/\"/\\\"/g' 
}

echo "let str : string = \"" > $TARGET

file_content $PROG_ENV >> $TARGET

echo "\"" >> $TARGET 