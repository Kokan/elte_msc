
const plant_name_empty = "<>";
const plant_name_cot   = "<carrot>";
const plant_name_crn   = "<corn>";
const plant_name_tto   = "<tomato>";

const plant_empty = 0;
const plant_cot   = 1;
const plant_crn   = 2;
const plant_tto   = 3;

function valid_task(task)
{
   if (!!task.cot && (task.cot <= 0 || task.cot > 5))
      return false;

   if (!!task.crn && (task.crn <= 0 || task.crn > 5))
      return false;

   if (!!task.tto && (task.tto <= 0 || task.tto > 5))
      return false;
      
   return true;
}

function plant(garden, round_no, task)
{
  if (!!task.cot && task.cot > 0)
  {
     garden[task.cot-1] = {plant: plant_cot, date: round_no };
  }

  if (!!task.crn && task.crn > 0)
  {
     garden[task.crn-1] = {plant: plant_crn, date: round_no };
  }

  if (!!task.tto && task.tto > 0)
  {
     garden[task.tto-1] = {plant: plant_tto, date: round_no };
  }

  if (!!task.empty && task.empty > 0)
  {
     garden[task.empty-1] = {plant: plant_empty, date: round_no };
  }
}

function bonus(plant1, plant2)
{
   const bonus_table = [
      [  0,  0,  0,  0 ],
      [  0, -1, +1, -1 ],
      [  0, +1, -1, +2 ],
      [  0, +2, +1, -1 ],
   ];

   return bonus_table[plant1][plant2];
}

function harvest(garden, round_no)
{
  var cot = 0;
  var crn = 0;
  var tto = 0;

  for (var i = 0; i < 5; ++i)
  {
  switch (garden[i].plant)
  {
   case plant_cot:
     if (garden[i].date + 2 == round_no+1)
        cot += 2
            +  ((i > 0) ? bonus(garden[i].plant, garden[i-1].plant) : 0)
            +  ((i < 4) ? bonus(garden[i].plant, garden[i+1].plant) : 0);
   break;
   case plant_crn:
     if (garden[i].date + 5 == round_no+1)
        crn += 7
            +  ((i > 0) ? bonus(garden[i].plant, garden[i-1].plant) : 0)
            +  ((i < 4) ? bonus(garden[i].plant, garden[i+1].plant) : 0);
   break;
   case plant_tto:
     if (garden[i].date + 4 == round_no+1)
        tto += 3
            +  ((i > 0) ? bonus(garden[i].plant, garden[i-1].plant) : 0)
            +  ((i < 4) ? bonus(garden[i].plant, garden[i+1].plant) : 0);
   break;
  }
  }

  return {
    cot: cot,
    crn: crn,
    tto: tto,
  };
}

function remove_dead_plant(garden, round_no)
{
  for (var i = 0; i < 5; ++i)
  {
  switch (garden[i].plant)
  {
   case plant_cot:
     if (garden[i].date + 2 == round_no+1)
        plant(garden, 0, {empty: i+1});
   break;
   case plant_crn:
     if (garden[i].date + 5 == round_no+1)
        plant(garden, 0, {empty: i+1});
   break;
   case plant_tto:
     if (garden[i].date + 4 == round_no+1)
        plant(garden, 0, {empty: i+1});
   break;
  }
  }
}

module.exports.garden_plant_reap_and_collect = function(number_of_rounds, planting_decisions)
{
  if (number_of_rounds != planting_decisions.length)
  {
    return { error: true };
  }

  var cot = 0;
  var crn = 0;
  var tto = 0;
  garden = Array.from({length: 5}, _ => new Object({plant: plant_empty, date: -1}))

  for (var i = 0; i < number_of_rounds; ++i)
  {
     if (!planting_decisions.reduce( (acc, task) => acc = acc  && valid_task(task), true))
        return { error: true };

     planting_decisions[i].forEach( task => plant(garden, i, task));

     units = harvest(garden, i);

     cot += units.cot;
     crn += units.crn;
     tto += units.tto;

     remove_dead_plant(garden, i);
  }


  return {
    cot: cot,
    crn: crn,
    tto: tto,
  };
}

module.exports.create_plant_decision = function(n)
{
 return Array.from({length: n}, _ => new Array(new Object()));
}
