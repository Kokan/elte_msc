const test = require('ava');
const garden = require('../plantgarden')


test('zero round, harvest nothing', t => {
	units = garden.garden_plant_reap_and_collect( 0, [] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

