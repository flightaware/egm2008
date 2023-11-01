#!/bin/sh

project_dir=$(pwd)

if [ ! -f egm.zip ]; then
  echo "===> Downloading egm.zip from earth-info.nga.mil..."
  curl -o egm.zip 'https://earth-info.nga.mil/php/download.php?file=egm-08interpolation'
else
  echo "===> Using existing egm.zip"
fi

echo "===> Verifying downloaded archive..."
if ! shasum -a 256 -c egm.zip.sha256; then
  echo "     Bailing due to bad checksum!"
  exit 1
fi

build_dir=$(mktemp -d)
echo "===> Unzipping egm.zip into $build_dir..."
unzip egm.zip -d "$build_dir"

echo "===> Installing generate.py..."
cp generate.py "$build_dir/generate.py"

echo "===> Entering $build_dir..."
cd "$build_dir" || exit 1

echo "===> Compiling Fortran interpolater..."
gfortran -o interpolate interp_2p5min.f

echo "===> Generating geoid.rs..."
python3 generate.py
mv geoid.rs "$project_dir/src/geoid.rs"

echo "===> Cleaning up $build_dir..."
rm -rf "$build_dir"
