use crate::geoid::{BAND_COUNT, BAND_SIZE, DATA};
use thiserror::Error;

mod geoid;

/// Errors indicate what went wrong calculating the geoid height.
#[derive(Error, Debug, PartialEq)]
pub enum Error {
    /// The supplied latitude was not in the expected range.
    #[error("latitude out of range")]
    LatitudeOutOfRange,
    /// The supplied longitude was not in the expected range.
    #[error("longitude out of range")]
    LongitudeOutOfRange,
}

/// Get the geoid height at the specified point on the globe.
///
/// The latitude must be in the range [-90, 90] inclusive, and the longitude must be in the range
/// [-180, 180] inclusive, otherwise an error will be returned.
///
/// The result is represented in meters above or below the WGS 84 ellipsoid.
///
/// # Examples
///
/// ```
/// # fn main() -> Result<(), egm2008::Error> {
///     let difference = egm2008::geoid_height(0.0, 0.0)?;
///     let message = format!("ground level is about {difference} meters above the WGS 84 ellipsoid");
///     assert_eq!(message, "ground level is about 17.225 meters above the WGS 84 ellipsoid");
///     Ok(())
/// }
/// ```
pub fn geoid_height(latitude: f32, longitude: f32) -> Result<f32, Error> {
    let latitude = Latitude::new(latitude)?;
    let longitude = Longitude::new(longitude)?;

    let (band_low, band_high) = latitude.bounding_bands();
    let (offset_low, offset_high) = longitude.bounding_offsets();

    // Look up the offsets at each of the four corners of the bounding box.
    let h00 = lookup_height(band_low, offset_low);
    let h01 = lookup_height(band_low, offset_high);
    let h10 = lookup_height(band_high, offset_low);
    let h11 = lookup_height(band_high, offset_high);

    // Interpolate a height for the actual lat/lon inside the bounding box.
    let latitude_scalar = latitude.interpolation_scalar();
    let longitude_scalar = longitude.interpolation_scalar();
    let latitude_lo = interpolate(h00, h10, latitude_scalar);
    let latitude_hi = interpolate(h01, h11, latitude_scalar);
    Ok(interpolate(latitude_lo, latitude_hi, longitude_scalar))
}

/// Latitude holds an f32 representing a WGS-84 latitude in degrees.
struct Latitude(f32);

impl Latitude {
    /// Create a new Latitude from the given f32, returning `Error::LatitudeOutOfRange` if the
    /// provided value is not between -90 and 90.
    fn new(latitude: f32) -> Result<Self, Error> {
        match latitude {
            latitude if (-90.0..=90.0).contains(&latitude) => Ok(Self(latitude)),
            _ => Err(Error::LatitudeOutOfRange),
        }
    }

    /// Return a translated and scaled version of the latitude for easier calculation of bands.
    ///
    /// The value is translated from the [-90, 90] range to the [0, 180] range, and then scaled down
    /// to the [0, 180/SCALE] range.
    fn translate_and_scale(&self) -> f32 {
        (self.0 + 90.0) / geoid::SCALE
    }

    /// Get a lower and upper band that contains this latitude.
    fn bounding_bands(&self) -> (usize, usize) {
        let lat = self.translate_and_scale();
        let low = lat.floor() as usize;
        let high = (low + 1).clamp(0, BAND_COUNT - 1);
        (low, high)
    }

    /// Figure out the proportion of the distance between the lower and upper bounds.
    fn interpolation_scalar(&self) -> f32 {
        let lat = self.translate_and_scale();
        let (lo, hi) = self.bounding_bands();
        let (lo, hi) = (lo as f32, hi as f32);
        if lo == hi {
            return 0.0;
        }
        (lat - lo) / (hi - lo)
    }
}

/// Latitude holds an f32 representing a WGS-84 longitude in degrees.
struct Longitude(f32);

impl Longitude {
    /// Create a new Longitude from the given f32, returning `Error::Longitude` if the
    /// provided value is not between -180 and 180.
    fn new(longitude: f32) -> Result<Self, Error> {
        match longitude {
            longitude if (-180.0..=180.0).contains(&longitude) => Ok(Self(longitude)),
            _ => Err(Error::LongitudeOutOfRange),
        }
    }

    /// Return a translated and scaled version of the longitude for easier calculation of offsets.
    ///
    /// The value is translated from the [-180, 180] range to the [0, 360] range, and then scaled
    /// down to the [0, 360/SCALE] range.
    fn translate_and_scale(&self) -> f32 {
        (self.0 + 180.0) / geoid::SCALE
    }

    /// Get a lower and upper offset that contains this longitude.
    fn bounding_offsets(&self) -> (usize, usize) {
        let lon = self.translate_and_scale();
        let low = lon.floor() as usize;
        let high = (low + 1).clamp(0, BAND_SIZE - 1);
        (low, high)
    }

    /// Figure out the proportion of the distance between the lower and upper offsets.
    fn interpolation_scalar(&self) -> f32 {
        let lon = self.translate_and_scale();
        let (lo, hi) = self.bounding_offsets();
        let (lo, hi) = (lo as f32, hi as f32);
        if lo == hi {
            return 0.0;
        }
        (lon - lo) / (hi - lo)
    }
}

/// Look up the height for the specified band/offset.
///
/// # Safety
///
/// This could panic if an invalid band/offset are specified. However, this can never happen due to
/// the validation we perform when constructing [`Latitude`] and [`Longitude`] and how we use the
/// scale factor generated by the Python script.
fn lookup_height(band: usize, offset: usize) -> f32 {
    DATA[band * BAND_SIZE + offset]
}

/// Given known values at `a` and `b`, construct a new value for a point that is `proportion` of the
/// way from `a` to `b`.
///
/// For example, if we know that F(5) = 1 and F(10) = 2, we can approximate that F(6), a value 20%
/// of the way between 5 and 10, will be 1.2 (a value 20% of the way between 1 and 2).
fn interpolate(a: f32, b: f32, proportion: f32) -> f32 {
    a + ((b - a) * proportion)
}

#[cfg(test)]
mod tests {
    use crate::{geoid_height, interpolate, Error};

    #[test]
    fn test_interpolate() {
        assert_eq!(interpolate(0.0, 100.0, 0.5), 50.0);
        assert_eq!(interpolate(100.0, 0.0, 0.5), 50.0);
        assert_eq!(interpolate(0.0, 0.0, 0.5), 0.0);
        assert_eq!(interpolate(5.0, 10.0, 0.2), 6.0);
    }

    #[test]
    fn fuzz_inputs() {
        let mut latitude = -90.0;
        while latitude <= 90.0 {
            let mut longitude = -180.0;
            while longitude <= 180.0 {
                assert!(
                    geoid_height(latitude, longitude).is_ok(),
                    "geoid_height({}, {}) caused a crash",
                    latitude,
                    longitude
                );
                longitude += 0.09;
            }
            latitude += 0.11;
        }
    }

    #[test]
    fn test_one_invalid_input() {
        let tests = [
            (-91.0, 0.0, Error::LatitudeOutOfRange),
            (91.0, 0.0, Error::LatitudeOutOfRange),
            (0.0, -181.0, Error::LongitudeOutOfRange),
            (0.0, 181.0, Error::LongitudeOutOfRange),
        ];
        for (lat, lon, expected) in tests {
            let result = geoid_height(lat, lon);
            assert!(
                result.is_err(),
                "Expected an error computing height for ({}, {})",
                lat,
                lon
            );
            if let Err(actual) = result {
                assert_eq!(expected, actual, "Got a different error than expected");
            }
        }
    }

    #[test]
    fn test_two_invalid_inputs() {
        assert!(geoid_height(-95.0, -200.0).is_err());
    }

    #[test]
    fn validate_known_points() {
        let tests = [
            (-90.0, -180.0, -30.15),
            (-90.0, 0.0, -30.15),
            (-90.0, 180.0, -30.15),
            (0.0, -180.0, 21.281),
            (0.0, 0.0, 17.225),
            (0.0, 180.0, 21.281),
            (90.0, -180.0, 14.899),
            (90.0, 0.0, 14.899),
            (90.0, 180.0, 14.899),
            (-81.0, -135.0, -45.184),
            (72.0, 141.0, -1.603),
            (-87.0, 49.5, -17.6775),
        ];
        for (lat, lon, expected) in tests {
            let result = geoid_height(lat, lon);
            assert!(
                result.is_ok(),
                "could not calculate geoid height at ({}, {})",
                lat,
                lon
            );
            if let Ok(actual) = result {
                assert_eq!(
                    actual, expected,
                    "got unexpected height at ({}, {})",
                    lat, lon
                );
            }
        }
    }
}
