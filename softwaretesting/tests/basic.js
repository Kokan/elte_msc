const test = require('ava');
const garden = require('../plantgarden')


test('zero round, harvest nothing', t => {
	units = garden.garden_plant_reap_and_collect( 0, [] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});


test('multiple round, no planting, harvest nothing', t => {
	units = garden.garden_plant_reap_and_collect( 1000, [] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});


test('one round, plant, carrot', t => {
	units = garden.garden_plant_reap_and_collect( 1, [{ cot: 1 }] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});


test('two round, plant, carrot', t => {
	units = garden.garden_plant_reap_and_collect( 2, [{ cot: 1 }] );
	t.is(units.cot, 2);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});


test('101 round, plant, carrot', t => {
	units = garden.garden_plant_reap_and_collect( 101, [{ cot: 1 }] );
	t.is(units.cot, 100);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('one round, plant, corn', t => {
	units = garden.garden_plant_reap_and_collect( 1, [{ crn: 1 }] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('two round, plant, corn', t => {
	units = garden.garden_plant_reap_and_collect( 2, [{ crn: 1 }] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('three round, plant, corn', t => {
	units = garden.garden_plant_reap_and_collect( 3, [{ crn: 1 }] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('four round, plant, corn', t => {
	units = garden.garden_plant_reap_and_collect( 4, [{ crn: 1 }] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('five round, plant, corn', t => {
	units = garden.garden_plant_reap_and_collect( 5, [{ crn: 1 }] );
	t.is(units.cot, 0);
	t.is(units.crn, 7);
	t.is(units.tto, 0);
});

test('101 round, plant, corn', t => {
	units = garden.garden_plant_reap_and_collect( 101, [{ crn: 1 }] );
	t.is(units.cot, 0);
	t.is(units.crn, 140);
	t.is(units.tto, 0);
});
