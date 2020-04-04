const test = require('ava');
const garden = require('../plantgarden')

test('create empty planting decision', t => {
	plant_decision = garden.create_plant_decision(0);
	t.is(plant_decision.length, 0);
});

test('create two length planting decision', t => {
	plant_decision = garden.create_plant_decision(2);
	t.is(plant_decision.length, 2);
	t.deepEqual(plant_decision[0], new Object());
	t.deepEqual(plant_decision[1], new Object());
});

test('zero round, harvest nothing', t => {
	units = garden.garden_plant_reap_and_collect( 0, garden.create_plant_decision(0) );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});


test('multiple round, no planting, harvest nothing', t => {
	units = garden.garden_plant_reap_and_collect( 1000, garden.create_plant_decision(1000) );
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
	units = garden.garden_plant_reap_and_collect( 2, [{ cot: 1 }, {}] );
	t.is(units.cot, 2);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});


test('101 round, plant, carrot', t => {
	decisions = garden.create_plant_decision(101);
	decisions[0] = {cot: 5};
	units = garden.garden_plant_reap_and_collect( 101, decisions );
	t.is(units.cot, 2);
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
	units = garden.garden_plant_reap_and_collect( 2, [{ crn: 1 }, {}] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('three round, plant, corn', t => {
	units = garden.garden_plant_reap_and_collect( 3, [{ crn: 1 }, {}, {}] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('four round, plant, corn', t => {
	units = garden.garden_plant_reap_and_collect( 4, [{ crn: 1 }, {}, {}, {}] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('five round, plant, corn', t => {
	units = garden.garden_plant_reap_and_collect( 5, [{ crn: 1 }, {}, {}, {}, {}] );
	t.is(units.cot, 0);
	t.is(units.crn, 7);
	t.is(units.tto, 0);
});

test('101 round, plant, corn', t => {
	decisions = garden.create_plant_decision(101);
	decisions[0] = {crn: 1};
	units = garden.garden_plant_reap_and_collect( 101, decisions );
	t.is(units.cot, 0);
	t.is(units.crn, 7);
	t.is(units.tto, 0);
});

test('one round, plant, tomato', t => {
	units = garden.garden_plant_reap_and_collect( 1, [{ tto: 1 }] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('two round, plant, tomato', t => {
	units = garden.garden_plant_reap_and_collect( 2, [{ tto: 1 }, {}] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('three round, plant, tomato', t => {
	units = garden.garden_plant_reap_and_collect( 3, [{ tto: 1 }, {}, {}] );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

test('four round, plant, tomato', t => {
	decisions = garden.create_plant_decision(4);
	decisions[0] = {tto: 1};
	units = garden.garden_plant_reap_and_collect( 4, decisions );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 3);
});

test('101 round, plant, tomato', t => {
	decisions = garden.create_plant_decision(101);
	decisions[0] = {tto: 5};
	units = garden.garden_plant_reap_and_collect( 101, decisions );
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 3);
});

test('37 round, plant, each', t => {
	decisions = garden.create_plant_decision(37);
	decisions[0] = {tto: 1, cot: 3, crn: 5};
	units = garden.garden_plant_reap_and_collect( 37, decisions );
	t.is(units.cot, 2);
	t.is(units.crn, 7);
	t.is(units.tto, 3);
});

test('37 round, plant carrot at round 37', t => {
	decisions = garden.create_plant_decision(37);
	decisions[36] = {cot: 5};
	units = garden.garden_plant_reap_and_collect( 37, decisions);
	t.is(units.cot, 0);
	t.is(units.crn, 0);
	t.is(units.tto, 0);
});

